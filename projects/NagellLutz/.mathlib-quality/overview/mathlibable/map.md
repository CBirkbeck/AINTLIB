# /mathlibable report — `IsEllDivSequence.map`

> Step-9 mathlibable assessment for the NagellLutz project (Nagell–Lutz theorem;
> elliptic curves; division polynomials; elliptic divisibility sequences).
> Target decl at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:640`.
>
> NOTE: this file was previously generated for the sibling decl `IsDivSequence.map`
> (line 637); both base names are `map`, so they share this filename. This report is
> for the **line-640** decl `IsEllDivSequence.map` (the task target) and supersedes
> the prior contents.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task brief; reasoned from source + upstream mathlib via WebFetch)
- decl `IsEllDivSequence.map`: ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:640`
                              (verbatim duplicate at `EllipticDivisibilitySequenceOriginal.lean:612`)
- kind:                      lemma (`theorem`)
- has sorry:                 no
- module docstring summary:  Elliptic divisibility sequences — forked + extended copy of
  `Mathlib.NumberTheory.EllipticDivisibilitySequence`. Copyright (c) 2024 David Kurniadi Angdinata
  (same author as the mathlib file). Adds an `EllSequence` namespace (`rel₃`/`rel₄`/`net`/`invar`
  machinery), the `Perm` development, the `.map` family, and complement-sequence API.

---

### Statement (Phase 1)

`IsEllDivSequence.map` states:

> If `f : R → S` is a ring homomorphism (any `F` with `[FunLike F R S] [RingHomClass F R S]`)
> and `W : ℤ → R` is an elliptic divisibility sequence, then `f ∘ W : ℤ → S` is an elliptic
> divisibility sequence.

Mathematically: **EDS are preserved under ring-homomorphism pushforward** (base change /
"reduction" — reduction mod p is the special case `f = ` the quotient map `ℤ → ℤ/pℤ`).

Variables / typeclasses (Lean side):
- `{R : Type u} {S : Type v} [CommRing R] [CommRing S]` — source/target comm rings.
- `(W : ℤ → R)` — the sequence.
- `{F} [FunLike F R S] [RingHomClass F R S] (f : F)` — the ring hom, bundled via `RingHomClass`.

Hypotheses (Lean side):
- `(h : IsEllDivSequence W)` — `W` is an EDS, i.e. `IsEllSequence W ∧ IsDivSequence W`.

Conclusion (math): `f ∘ W` is an EDS over `S`.
Conclusion (Lean): `IsEllDivSequence (f ∘ W)`.

Body (a pairing of the two component `.map` lemmas — effectively one expression):
```lean
lemma IsEllDivSequence.map (h : IsEllDivSequence W) : IsEllDivSequence (f ∘ W) :=
  ⟨h.1.map f, h.2.map f⟩
```
where the two components (same file, lines 634 / 637) are:
```lean
lemma IsEllSequence.map (h : IsEllSequence W) : IsEllSequence (f ∘ W) := fun m n r => by
  simpa only [Rel₃, Function.comp_apply, map_mul, map_pow, map_sub] using congr_arg f (h m n r)
lemma IsDivSequence.map (h : IsDivSequence W) : IsDivSequence (f ∘ W) :=
  (map_dvd f <| h · · ·)
```

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: helper "functoriality" glue lemma; not a named theorem, not a new structure, not a
`## Main results` entry. (Lit width is exhaustive regardless.)

### One-line check (Phase 2b)

Body: a single anonymous-constructor pairing `⟨h.1.map f, h.2.map f⟩` → treat as ONE-LINER.
One-liner verdict: **ONE-LINER** (pure glue over the two component lemmas).

| Exemption                         | Applies? | Evidence                                                                 |
|-----------------------------------|----------|--------------------------------------------------------------------------|
| Avoid defeq abuse                | no       | no downstream proof depends on a sealed RHS spelling                     |
| Avoid typeclass diamonds         | no       | not a `def`/`instance`; introduces no instance                          |
| Mark semantic intent / API name  | yes      | `.map` dot-notation on an `IsEllDivSequence` hypothesis (`h.map f`) is the API surface; mirrors the existing `.smul` family and mathlib's `map_normEDS`/`map_complEDS` naming convention |

Conclusion: **ONE-LINER WITH-EXEMPTION** (semantic API anchor). It is the EDS-*predicate* analogue
of the `map_*` lemmas mathlib already ships for the *concrete* sequences.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                   | Hit? | Standard form found                              | Notes |
|----|----------------------------------|---------------------------------------------------------------------------------------------------------|------|--------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | mathlib IsEllDivSequence map RingHomClass elliptic divisibility sequence                                 | yes  | mathlib EDS module exists; only concrete-sequence `map_*` lemmas | predicate-level `.map` not present upstream |
|  2 | WebSearch (general form)         | EDS reduction mod p / base change / ring homomorphism functorial (Ward, Stange)                          | yes  | reduction-mod-p of EDS is standard (Ward periodicity; p-adic papers) | functoriality treated as a trivial structural remark, not a named theorem |
|  3 | WebSearch (named-after/aliases)  | "divisibility sequence" preserved under ring homomorphism / polynomial-identity functor                 | part | divisibility sequences generalise to ideals/posets; pushforward implicit | no citable "name" for the pushforward lemma |
|  4 | ChatGPT MCP                      | (functoriality + generality question, drafted)                                                          | n/a  | —                                                | MCP/Codex down in this env (errored on call); used WebSearch fallback per task brief |
|  5 | Local references                 | `.mathlib-quality/references/` for "EDS / divisibility sequence / map"                                  | n/a  | (no references dir for this project)             | recorded n/a |
|  6 | nLab                             | divisibility sequence / functoriality                                                                   | no   | nLab has no "divisibility sequence" page         | concept lives in NT, not category theory |
|  7 | nCatLab                          | —                                                                                                       | n/a  | —                                                | not a categorical concept |
|  8 | Stacks Project                   | —                                                                                                       | n/a  | —                                                | not a scheme-theoretic concept; EDS is elementary NT |
|  9 | MathOverflow / MSE               | divisibility sequence pushforward / reduction generality                                                | part | base-change of EDS is folklore                   | no dedicated named result |
| 10 | recent arXiv (≤5 yr)             | Stange "Division Polynomials for Arbitrary Isogenies" (2025); genus-2 periods mod p (2023, 2310.01013)  | yes  | reduction/base-change ubiquitous, never named    | confirms it is a structural triviality |

The protocol passed: WebSearch ran 3 queries at distinct generality levels; ChatGPT MCP recorded
n/a-with-reason (tool down); local refs n/a-with-reason; nLab/Stacks/MathOverflow/arXiv each
checked or n/a-with-reason.

### Literature summary (Phase 3)

Concept identified as: **functoriality / base change of elliptic divisibility sequences under a
ring homomorphism** (`reduction` is the special case of a quotient map).
Sources agree on the standard form: yes — and they agree it is a *trivial structural remark*, not a
named/citable theorem. Reduction mod p of an EDS is everywhere in the literature (Ward 1948
periodicity; Silverman's p-adic-properties paper math/0404412; Stange's elliptic nets), always
invoked in passing.
Most general standard form: for any ring hom `f : R → S`, applying `f` to the defining polynomial
identity (which uses only `+`, `−`, `*`, powers — all preserved by a ring hom) preserves the
elliptic-sequence equation; and `m ∣ n ⟹ W m ∣ W n` pushes through any divisibility-preserving
(monoid-hom-class) map. Both halves are preserved.
Generality dimensions where the literature varies:
  - the map: usually "ring homomorphism" (often the reduction map specifically). The elliptic
    identity genuinely needs `+` and `*` (ring hom); the divisibility half needs only a
    multiplicative/`MonoidHomClass` map.
Disagreement with the literature: **none.** The Lean form (`RingHomClass`) matches the literature's
"apply a ring hom" exactly.

---

### Generality analysis — `IsEllDivSequence.map`

Literature-standard form: for any ring hom `f`, `f∘W` is an EDS whenever `W` is.

| # | Parameter / hypothesis              | Current Lean form                  | Literature-standard form         | Weaker form exists? | Reason |
|---|-------------------------------------|------------------------------------|----------------------------------|---------------------|--------|
| 1 | `[FunLike F R S] [RingHomClass F R S] (f : F)` | bundled ring hom via class | ring homomorphism                | NO (for the whole)  | the elliptic identity needs `map_mul` + `map_sub` + `map_pow`; ring hom is exactly right. **Already maximally idiomatic** — uses `RingHomClass`, not a bare `R →+* S`, so it also accepts `R ≃+* S`, evaluation homs, etc. |
| 2 | `[CommRing R] [CommRing S]`         | commutative rings                  | comm ring (EDS defined over CommRing) | NO              | the EDS predicate itself is stated over `CommRing` in mathlib; can't weaken below the ambient theory |

Note on the *component* lemma `IsDivSequence.map` (a dependency): its proof uses only `map_dvd f`,
which holds for `MonoidHomClass`. So `IsDivSequence.map` alone could be stated more generally
(monoid hom). But the combined `IsEllDivSequence.map` needs the full ring hom for its elliptic
half, so `RingHomClass` is the correct typeclass for *this* lemma.

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (for the EDS-pushforward statement).
Number of weakening opportunities found: 0 for `IsEllDivSequence.map` itself (the `RingHomClass`
bundling is already the modern idiom — strictly more general than `R →+* S`).
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Reformulation | Downstream |
|----|--------------------------------------------------------------------------|----------|---------------|------------|
|  1 | bundled-hyp → typeclass/instance?                                        | no       | already uses `RingHomClass` (typeclass form) | — |
|  2 | sequences/metric → filters/topology?                                     | no       | finite algebraic identity; no topology | — |
|  3 | construct object → universal-property class?                            | no       | it's a predicate-preservation lemma | — |
|  4 | set+closure-pred → bundled substructure?                                | no       | — | — |
|  5 | vector-space/field-specific → weaken typeclass?                         | no       | already at `CommRing` + `RingHomClass`, the floor for EDS | — |
|  6 | 1-categorical → higher-categorical?                                     | no       | — | — |
|  7 | concrete index → general additive structure?                           | no       | EDS are intrinsically ℤ-indexed (the recurrence is over ℤ) | — |

Modern idiom available: **no**. The lemma already uses the contemporary `RingHomClass` bundling and
sits at the floor typeclass for its theory. One-line reason: nothing to modernise — it is already
the Bourbaki-2.0 spelling of "EDS pushforward".

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities / typeclass-search paths introduced).

---

### Mathlib search-status: `IsEllDivSequence.map`

[A] Lean-Finder       "EDS preserved ring hom", "IsEllDivSequence map"   no hits (index covers concrete `map_*` only)
[B] Loogle            `IsEllDivSequence (_ ∘ _)`, `IsEllSequence (⇑_ ∘ _)`   no hits
[C] LeanSearch        "elliptic divisibility sequence image under ring homomorphism"   no hits at predicate level
[D] Grep mathlib src  `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (pin `d90090f` on disk **and** GitHub master via WebFetch) for `IsEllSequence.map`, `IsEllDivSequence.map`, `f ∘ W`, `RingHomClass`, `FunLike`   **NO HITS** — section `IsEllDivSequence` ends right after the three `.smul` lemmas (mathlib line 116); the predicate section has no `RingHomClass`/`FunLike` variable at all
[E] Name pattern      grep whole repo for `IsEllDivSequence.map` / `IsEllSequence.map` / `IsDivSequence.map`   present **only in this project's fork** (and its `…Original.lean` copy); HasseWeil has a `private` re-derivation `IsEllSequence.map'` (`projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:666`)

Searched for both the user's form and the literature-standard (more general) form.

**Mathlib DOES ship the analogous lemmas for the *concrete* sequences** — `map_preNormEDS`,
`map_normEDS`, `map_complEDS₂`, `map_complEDS'`, `map_complEDS` (e.g. `f (normEDS b c d n) =
normEDS (f b) (f c) (f d) n`) — but **nothing** that pushes the abstract
`IsEllSequence` / `IsDivSequence` / `IsEllDivSequence` *predicate* through a ring hom.

Verified against **current mathlib master** (GitHub raw), not just the pinned `d90090f`: still
absent. Also confirmed mathlib's `IsDivSequence` is **ℕ-indexed** (`∀ m n : ℕ, …`) whereas this
project's is **ℤ-indexed** (`∀ m n : ℤ, …`) — a definition-level divergence in the fork (see Phase 7).

Concluded: **not in mathlib** (all 5 methods exhausted, incl. the literature-standard form, incl.
current master). The predicate-level `.map` is a genuine gap; the concrete-sequence `map_*` family
is the existing precedent it would slot beside.

---

### Call sites — `IsEllDivSequence.map`

Internal use count (this project, excluding the declaring file): **0** direct callers of
`IsEllDivSequence.map`.
External-to-file callers: 0 direct (but see re-derivations below).

| Caller file:line               | Usage pattern                                                       |
|--------------------------------|---------------------------------------------------------------------|
| (none call `IsEllDivSequence.map` directly)                       |                          |

Inline-derivation / duplication grep (the equivalent re-derived elsewhere):
  - `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequenceOriginal.lean:606-612` — a second,
    nearly-identical copy of all three `.map` lemmas (older draft of this same file).
  - `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:666` — `private lemma
    IsEllSequence.map'` re-derives the elliptic half independently (`f : R →+* S`), used to prove
    `IsEllSequence.normEDS`.

Interpretation (Phase 6.0.1 / feedback into Phase 2b): `K = 0` direct uses of the *triple* glue
lemma, BUT the underlying pushforward is **re-derived in ≥2 other places across the repo**
(HasseWeil's `IsEllSequence.map'`, the `…Original.lean` copy). Per the call-sites table this is the
"re-derived inline elsewhere" pattern → the API is genuinely wanted; it is just **duplicated rather
than centralised**. The component `IsEllSequence.map` is the load-bearing piece (HasseWeil needs it
for `normEDS`); the `IsEllDivSequence.map` triple is the convenience wrapper over it.

---

### Composition check (Phase 6)

Can `IsEllDivSequence.map` be derived from mathlib in ≤3 chained calls? **No — there is nothing in
mathlib to chain.** The proof is `⟨h.1.map f, h.2.map f⟩`, but `IsEllSequence.map` and
`IsDivSequence.map` are themselves *not in mathlib* (Phase 5). So the "composition" would be over
the project's own helpers, not mathlib primitives.

Attempt 1 (push the predicate directly from mathlib): there is no mathlib lemma taking
`IsEllSequence W` to `IsEllSequence (f ∘ W)`. The concrete `map_normEDS` etc. operate on
`normEDS`/`complEDS`, not on an arbitrary `W` satisfying the predicate. Result: **fails** — wrong shape.

Attempt 2 (re-prove from scratch at a call site): one *could* inline
`fun m n r => by simpa [...] using congr_arg f (h.1 m n r)` for the elliptic half and
`map_dvd f <| h.2 · · ·` for the divisibility half. But that is exactly re-deriving the two
component lemmas — i.e. duplicating `IsEllSequence.map` + `IsDivSequence.map` — not a mathlib
composition. This is precisely what HasseWeil's `IsEllSequence.map'` does, demonstrating the
duplication cost of NOT having it centrally.

Conclusion: **NOT-COMPOSABLE from mathlib.** (Composable from the project's own `.map` components,
but those don't exist upstream — so the right unit to upstream is the family, not an inline.)

---

## Verdict: `IsEllDivSequence.map`

**Category:** `YES-add-as-is`

**Evidence:**
- Literature search (Phase 3): functoriality/base-change of EDS under a ring hom is standard and
  matches the Lean form exactly; treated as a structural fact (so no "more general named form" to
  chase). Generality already maximal.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** — uses `RingHomClass` (modern idiom, more
  general than `R →+* S`); Phase 4c found nothing to modernise.
- Mathlib search (Phase 5): **not in mathlib** (verified on pin `d90090f` *and* current master);
  mathlib ships the analogous `map_*` lemmas only for the *concrete* sequences, not the predicate.
- Composition check (Phase 6): **NOT-COMPOSABLE** from mathlib (nothing upstream to chain).

**Rationale:**

Mathlib's `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` defines exactly the
`IsEllSequence` / `IsDivSequence` / `IsEllDivSequence` predicates and already establishes the
ring-hom-pushforward principle for every *concrete* sequence it builds — `map_preNormEDS`,
`map_normEDS`, `map_complEDS₂`, `map_complEDS'`, `map_complEDS`. The one missing companion is the
*predicate-level* statement: "if `W` satisfies `IsEllDivSequence`, so does `f ∘ W`". That gap is
real and is being paid for repeatedly inside AINTLIB — HasseWeil re-derives the elliptic half as a
`private` lemma `IsEllSequence.map'` to prove `IsEllSequence.normEDS`, and an older copy of this
file re-derives the whole family. Centralising it upstream removes that duplication and gives
"reduction mod p of an EDS is an EDS" (the `f = ` quotient-map special case) as a one-liner, which
is the workhorse fact in the Ward/Silverman p-adic line of results.

The form is already maximal: `RingHomClass` (so it accepts `R →+* S`, `R ≃+* S`, evaluation homs,
the reduction map, …), `CommRing` (the floor for the EDS theory), no weakenings available, and
Phase 4c found no modernisation. It is a one-liner, but it carries a genuine API exemption — it is
the EDS-predicate sibling of mathlib's existing `map_*` naming family and the dot-notation anchor
(`h.map f`) other developments call — so the one-liner-without-exemption bias does not apply.

**WHY add it (refactor-actionable):**
- *New content vs mathlib:* the predicate-level pushforward of `IsEllSequence` / `IsDivSequence` /
  `IsEllDivSequence`. Mathlib has the concrete-sequence `map_*` lemmas but no predicate version —
  a named, recurring gap (HasseWeil's `IsEllSequence.map'` exists *only* because the upstream
  lemma is missing).
- *The specific gap:* `Mathlib.NumberTheory.EllipticDivisibilitySequence` has a `Map` section
  (the `map_normEDS`/`map_complEDS` lemmas) but it stops at the *constructions*; the *predicates*
  defined ~400 lines earlier get `isEllSequence_id` and the `.smul` family but no `.map`. The three
  `.map` lemmas are the obvious missing siblings of the three `.smul` lemmas already upstream.
- *How it composes:* gives base-change/reduction of EDS for free (`f` = `Int.castRingHom`,
  `algebraMap`, the `ZMod p` reduction map, MvPolynomial `aeval`, …); `IsEllSequence.map` in
  particular is what lets `normEDS` over a general ring inherit ellipticity from the universal
  polynomial ring (exactly HasseWeil's `IsEllSequence.normEDS` use).

**IMPORTANT divergence to resolve before/at PR time (the one real wrinkle):**
This project changed `IsDivSequence` from mathlib's **ℕ-indexed** `∀ m n : ℕ, m ∣ n → W m ∣ W n`
to **ℤ-indexed** `∀ m n : ℤ, m ∣ n → W m ∣ W n`. Consequences:
  - `IsEllSequence.map` is **identical** to mathlib's predicate (no divergence) → upstreams cleanly.
  - `IsDivSequence.map` and hence `IsEllDivSequence.map` are stated against the **project's**
    ℤ-indexed `IsDivSequence`, which is *not* mathlib's. The lemma proof (`map_dvd f`) is
    index-agnostic and works for either, but the PR must either (a) upstream against mathlib's
    existing ℕ-indexed `IsDivSequence`, or (b) be bundled with a separate proposal to generalise
    mathlib's `IsDivSequence` to ℤ. This is a packaging question, **not** a reason to downgrade the
    verdict (the lemma content is wanted either way).

Proposed mathlib location:    `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
                              (in the `IsEllDivSequence` section, right after the `.smul` trio at
                              what is currently mathlib line ~114, mirroring their placement).
Proposed PR title:            "feat(NumberTheory): EDS predicates are preserved under ring-hom pushforward"
PR grouping:                  ship the **three together** — `IsEllSequence.map`, `IsDivSequence.map`,
                              `IsEllDivSequence.map` — as one PR (they are the `.smul` family's
                              mirror image and share the `RingHomClass` variable block). Reconcile
                              the ℕ-vs-ℤ `IsDivSequence` index in the same PR.
Pre-PR checklist before opening:
  - [ ] Resolve the ℕ-vs-ℤ `IsDivSequence` divergence (upstream against mathlib's current def, or
        co-propose the ℤ generalisation).
  - [ ] `/generalise IsDivSequence.map` — consider stating the divisibility half at
        `MonoidHomClass` (it only uses `map_dvd`), even if `IsEllDivSequence.map` keeps `RingHomClass`.
  - [ ] `/cleanup` the trio (style + naming + confirm the `simpa only [...]` lemma set is minimal).
  - [ ] After upstreaming, delete HasseWeil's `private IsEllSequence.map'` and the
        `…Original.lean` duplicate; re-point them at the mathlib lemma.
  - [ ] Pick a reviewer from recent `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
        committers (the file's original author is this project's author — coordinate, since the fork
        is theirs).

---

## Next step

Run the pre-PR checklist above — chiefly **resolve the ℕ-vs-ℤ `IsDivSequence` index divergence** —
then open one PR adding `IsEllSequence.map` / `IsDivSequence.map` / `IsEllDivSequence.map` to
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` beside the existing `.smul` trio, and
afterwards de-duplicate HasseWeil's `IsEllSequence.map'` and the `…Original.lean` copy against it.
