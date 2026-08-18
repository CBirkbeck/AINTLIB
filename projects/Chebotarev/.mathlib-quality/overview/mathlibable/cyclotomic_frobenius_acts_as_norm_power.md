# /mathlibable report — `Chebotarev.cyclotomic_frobenius_acts_as_norm_power`

## Baseline (Phase 0)

- lake build:               not run (local build known stale per task; reasoned from source — the
                            decl elaborates as written, all referents resolve in the repo and in the
                            pinned mathlib `.lake/packages/mathlib`)
- decl `Chebotarev.cyclotomic_frobenius_acts_as_norm_power`: ✓ resolved at
                            `projects/Chebotarev/CebotarevDensity/CyclotomicNormResidue.lean:52`
- qualified name:           `Chebotarev.cyclotomic_frobenius_acts_as_norm_power`
                            (`namespace Chebotarev` opens at line 36; no nested namespace; theorem at 52)
- kind:                     theorem
- has sorry:                no
- module docstring summary: "The cyclotomic Frobenius as a norm residue, and Frobenii generate" —
                            two arithmetic inputs to the Frobenius-fibre equidistribution, placed
                            below `ZetaProduct.lean` in the import order.

---

## Statement (Phase 1)

`Chebotarev.cyclotomic_frobenius_acts_as_norm_power` is a **theorem** (Sharifi 7.2.1 step (i),
p. 142 — "we have φ_𝔭(ζ_m) = ζ_m^{N𝔭} for a primitive mth root of unity ζ_m") stating:

Let `K` be a number field, `m ≥ 1`, and `L = K(μ_m)` the `m`-th cyclotomic extension
(`IsCyclotomicExtension {m} K L`, `IsGalois K L`). Let `𝔭` be a prime of `𝓞 K` **unramified in `L`**
with **`N𝔭` coprime to `m`**, and let `𝔓` be a prime of `𝓞 L` lying over `𝔭`. Then the **arithmetic
Frobenius automorphism at `𝔓`** (`arithFrobAt (𝓞 K) Gal(L/K) 𝔓`, the canonical element of `Gal(L/K)`
characterised by `σ x ≡ x^{N𝔭} (mod 𝔓)`) sends **every primitive `m`-th root of unity `ζ ∈ L`** to
`ζ^{N𝔭}`:

  `arithFrobAt (𝓞 K) Gal(L/K) 𝔓 ζ = ζ ^ Ideal.absNorm 𝔭`.

This is the **element-level** form of the cyclotomic-Frobenius / Artin-automorphism formula. Its
multiplicative-character repackaging is the sibling `Chebotarev.autToPow_frobeniusClass_out`
(`χ(Frob_𝔭) = N𝔭 mod m`), which is the *only* consumer of this lemma.

Variables / typeclasses (Lean side):
- `K L : Type*`, `[Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]` —
  the number-field cyclotomic extension `L/K`.
- `m : ℕ`, `[NeZero m]`, `[IsCyclotomicExtension {m} K L]` — `L = K(μ_m)`.
- `(𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime]` — the prime of the base.
- `(𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hP : 𝔓.LiesOver 𝔭)` — a chosen prime above it.

Hypotheses (Lean side):
- `hunr : UnramifiedIn K L 𝔭` — `𝔭` unramified in `L` (project-local predicate; provides the finite
  residue field `Finite (𝓞 L ⧸ 𝔓)`, which the `haveI` in the conclusion uses).
- `hcop : (Ideal.absNorm 𝔭).Coprime m` — residue characteristic ∤ m (so `ζ` stays primitive mod 𝔓;
  used to prove `(m : 𝓞 L) ∉ 𝔓`, the hypothesis `apply_of_pow_eq_one` needs).

Conclusion (math): `Frob_𝔓(ζ) = ζ^{N𝔭}` for every primitive `m`-th root of unity `ζ`.

Conclusion (Lean):
`∀ ζ : L, ζ ∈ primitiveRoots m L → arithFrobAt (𝓞 K) Gal(L/K) 𝔓 ζ = ζ ^ Ideal.absNorm 𝔭`
(under `haveI : Finite (𝓞 L ⧸ 𝔓) := …`).

---

## Size classification (Phase 2a)

Verdict: **BIG** (borderline; recorded BIG for framing).
Reason: it is a named classical arithmetic theorem (the cyclotomic / Artin–Frobenius formula
`Frob_𝔭(ζ) = ζ^{N𝔭}`, Sharifi §7.2 / Washington *Cyclotomic Fields*) and a load-bearing arithmetic
input of the project's Chebotarev-density development — not a one-step helper. Literature width is
EXHAUSTIVE regardless.

## One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure` — one-liner check is **n/a**. The proof body is
~25 substantive lines: build `z = hζ.toInteger` with `z^m = 1`; establish `(m : 𝓞 L) ∉ 𝔓` from
`hcop` (via `absNorm_span_singleton` + `Algebra.norm_algebraMap` + the coprimality, ~8 lines);
identify `q = absNorm 𝔭` with `Nat.card (𝓞 K ⧸ 𝔓.under (𝓞 K))`; call the mathlib engine
`(IsArithFrobAt.arithFrobAt …).apply_of_pow_eq_one hzpow hmnotmem`; then transport the resulting
`𝓞 L`-equality to `L` along `algebraMap (𝓞 L) L`.

---

## PHASE 3 — Literature search (EXHAUSTIVE)

### Literature search table

| #  | Channel                          | Query                                                                                                   | Hit? | Standard form found                                                              | Notes |
|----|----------------------------------|---------------------------------------------------------------------------------------------------------|------|----------------------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "Frobenius automorphism cyclotomic field acts on root of unity as ζ raised to norm of prime ideal number field" | yes  | `σ(α) ≡ α^p (mod 𝔭)`; on roots of unity `σ(ζ)=ζ^{N𝔭}`, `N𝔭 = p^f`              | Park REU 2015 ("Existence of the Frobenius element"); Meli REU 2013; CMU cyclotomic-function-fields notes; Columbia §7 Cyclotomic Extensions — all state `Frob` raises ζ to the residue-norm power |
|  2 | WebSearch (named/general form)   | `"Frob" cyclotomic "ζ^{N" prime norm residue Galois number field standard theorem Sharifi Washington`    | yes  | `σ(ζ)=ζ^{a_σ}`, `a_σ = p mod m`; general-base form via `N𝔭`                       | **Sharifi `cycl.pdf` (the project's cited source)**; K. Conrad "Cyclotomic Extensions"; Stanford Math 210B (Conrad) cyclotomic handout; Wikipedia "Cyclotomic field" |
|  3 | WebSearch (Artin-map alias)      | (covered by #1/#2 hits + prior `autToPow_frobeniusClass_out` channel-3 sweep)                            | yes  | Artin automorphism `ζ_m ↦ ζ_m^{N𝔭}`; image of `D_𝔓` is `⟨N𝔭 mod m⟩`              | MIT 18.785 Lect. 7 & 21; "every abelian ext of `K` lies in a cyclotomic field" stated over general `K` |
|  4 | ChatGPT MCP                      | (standard name + generality of base field + CFT-free vs Artin; idiomatic Lean form)                     | n/a  | —                                                                                | **MCP down** (matches the task's "ChatGPT math MCP may be down" warning); compensated by extra WebSearch + direct mathlib-source reading |
|  5 | Local references                 | grep `.mathlib-quality/references/` and `refs/Chebotarev/` for "cyclotomic"/"Frobenius"                  | n/a  | (no `references/` dir; no `refs/` store on this machine)                          | Both directories absent — recorded n/a. Docstring cites Sharifi 7.2.1 step (i), p. 142, verbatim |
|  6 | nLab                             | "cyclotomic character Frobenius prime roots of unity Galois"                                             | partial | cyclotomic character = Galois action on roots of unity; `χ_p(Frob_ℓ)=ℓ` (ℚ-level) | nLab page itself not surfaced; the ℚ-level content is the Wikipedia "Cyclotomic character" `χ_p(Frob_ℓ)=ℓ` |
|  7 | nCatLab (if categorical)         | —                                                                                                       | n/a  | not a categorical concept                                                          | Arithmetic Galois theory; no higher-categorical content |
|  8 | Stacks Project (if alg geom)     | —                                                                                                       | n/a  | not a scheme-theoretic statement                                                  | Number-field Frobenius on roots of unity; outside Stacks' scope |
|  9 | MathOverflow / Math.StackExchange| (covered transitively by #1/#2: REU notes, Conrad/Stanford handouts)                                     | yes  | same `ζ ↦ ζ^{N𝔭}` consensus                                                       | Park, Meli, Conrad corroborate; no dispute on the form |
| 10 | recent arXiv (last 5 years)      | (surfaced in #1: arXiv 1511.01755 "order modulo p of an algebraic number")                               | yes  | uses `Frob(ζ)=ζ^{Nq}` as standard background                                       | Classical bedrock, not a novel/recent result |

### Literature summary (Phase 3)

Concept identified as: **the cyclotomic / Artin–Frobenius automorphism formula**, element form:
`Frob_𝔭(ζ_m) = ζ_m^{N𝔭}`. The `K = ℚ` shadow is `σ(ζ_m) = ζ_m^p` with the canonical isomorphism
`(ℤ/mℤ)ˣ ≅ Gal(ℚ(ζ_m)/ℚ)`; over a number field the exponent is the residue norm `N𝔭 = p^f`.

Sources agree on the standard form: **yes**. Classical bedrock of algebraic number theory
(Washington *Cyclotomic Fields*; Sharifi notes §7.2, the project's cited source; K. Conrad/Stanford
handouts; MIT 18.785; every CFT course). It is the defining property of the Frobenius restricted to
the roots of unity.

Most general standard form: **arbitrary number-field base `K`**, `L = K(μ_m)`, `𝔭` unramified with
`N𝔭` coprime to `m`; `Frob_𝔭(ζ) = ζ^{N𝔭}` — exactly the project's form.

Generality dimensions where the literature varies:
  - Base field: from `ℚ` (most common pedagogical statement) to **arbitrary number field `K`**
    (the project's form — fully standard; the cyclotomic case of the Artin map).
  - Packaging: (a) **element form** `Frob_𝔭(ζ)=ζ^{N𝔭}` (this lemma); (b) **character form**
    `χ(Frob_𝔭)=N𝔭 mod m` (the sibling `autToPow_frobeniusClass_out`); (c) decomposition-group form
    (image of `D_𝔓` = `⟨N𝔭 mod m⟩`). This lemma provides (a) on a chosen `𝔓`; mathlib provides
    (c) over `ℚ` only (Phase 5).
  - Provenance: deduced CFT-free for the cyclotomic case (the proof here is CFT-free, routed through
    the residue-field Frobenius power law `φ ζ = ζ^q`), then subsumed by Artin reciprocity.

Disagreement with the literature: **none**. The project's form is the standard general-base element
form.

---

## PHASE 4 — Generality analysis

### Generality status table — `Chebotarev.cyclotomic_frobenius_acts_as_norm_power`

Literature-standard form (Phase 3): general number field `K`, `L = K(μ_m)`, `𝔭` unramified with `N𝔭`
coprime to `m`; `Frob_𝔭(ζ) = ζ^{N𝔭}` (element form).

| # | Parameter / hypothesis                       | Current Lean form                  | Literature-standard form                   | Weaker form exists? | Reason it can/can't be weakened |
|---|----------------------------------------------|------------------------------------|--------------------------------------------|---------------------|---------------------------------|
| 1 | `[NumberField K]` (base field)               | arbitrary number field             | arbitrary number field                     | NO (already general)| This IS the general base; mathlib has only the `ℚ` specialisation (`galEquivZMod_apply_of_pow_eq`). Not narrower than standard. |
| 2 | `[IsCyclotomicExtension {m} K L]`            | `L = K(μ_m)`                       | `L = K(μ_m)`                               | NO                  | Intrinsic to the cyclotomic statement. |
| 3 | `(hunr : UnramifiedIn K L 𝔭)`               | unramified in `L`                  | unramified (equiv. `𝔭 ∤ m` for nontrivial) | partial (see below) | Used only to supply `Finite (𝓞 L ⧸ 𝔓)`. The mathlib engine `apply_of_pow_eq_one` does NOT need unramifiedness — only `(m : 𝓞 L) ∉ 𝔓` (which follows from `hcop`) and a Frobenius at `𝔓`. So `hunr` is partly redundant with `hcop` for *this* element statement (it matters for the *uniqueness/conjugacy* of the Frobenius, packaged elsewhere). Standard hypothesis to state nonetheless. |
| 4 | `(hcop : (Ideal.absNorm 𝔭).Coprime m)`      | `N𝔭` coprime to `m`                | `N𝔭` coprime to `m` (residue char ∤ m)     | NO                  | Genuinely necessary (docstring argues this): drives `(m : 𝓞 L) ∉ 𝔓`; without it `ζ` collapses mod `𝔓`. |
| 5 | `(𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hP : 𝔓.LiesOver 𝔭)` | a chosen prime above `𝔭`   | the Frobenius at a chosen `𝔓` (or the class) | n/a (packaging)   | The literature states it per-`𝔓` (or per-class via conjugacy); this matches. The character form (sibling) abstracts over the conjugacy class. |
| 6 | exponent `Ideal.absNorm 𝔭`                   | absolute norm `N𝔭` (over `ℤ`)      | residue norm `N𝔭 = #(𝓞K/𝔭)`               | NO                  | `absNorm 𝔭 = #(𝓞 K ⧸ 𝔭) = #(𝓞 K ⧸ 𝔓.under)` (the proof's `hqcard`); identical to the standard exponent. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (in the literature sense). The base field is already an
arbitrary number field — strictly *more* general than mathlib's `ℚ`-only counterpart
(`IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq`, Phase 5). All hypotheses are the standard
ones; `hcop` and the cyclotomic/unramified setup are the necessary cluster.

Number of weakening opportunities found: **0 genuine generality weakenings** (row 3 notes `hunr` is
partly redundant with `hcop` *for the element statement alone*, but dropping it would change the API
contract — it's what guarantees the finite residue field appearing in the conclusion's `haveI`, and
keeps this lemma in step with its only consumer; this is a packaging nuance, not a generalisation).
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                       | Applies? | Proposed reformulation                                                                  | Mathlib downstream this enables |
|----|------------------------------------------------------------------------------------------------|----------|------------------------------------------------------------------------------------------|---------------------------------|
|  1 | "let X be a foo" preambles → typeclasses?                                                       | no       | already fully typeclass-driven (`IsCyclotomicExtension`, `IsGalois`, `NumberField`, `𝔓.IsPrime`, `𝔓.LiesOver 𝔭`) | — |
|  2 | sequences/metric → filters/topological?                                                         | no       | finite/arithmetic statement; no limit content                                            | — |
|  3 | construct an object where a universal property would characterise it?                           | no       | it is a *theorem* (an equality in `L`), not a construction                                | — |
|  4 | set-with-closure-predicate → bundled substructure?                                              | no       | no substructure here                                                                      | — |
|  5 | vector-space/metric/field-specific → weaker typeclass?                                          | **yes (already realised by mathlib's engine)** | The element-engine is already stated by mathlib over an **abstract ring extension with a group action and an arbitrary arithmetic Frobenius** (`AlgHom.IsArithFrobAt.apply_of_pow_eq_one`, `RingTheory/Frobenius.lean:109`): `φ ζ = ζ ^ Nat.card (R ⧸ Q.under R)` for `ζ^m=1`, `↑m ∉ Q`, `S` a domain. The number-field cyclotomic statement is a **specialisation** of that. | The abstract form already composes with the whole `IsArithFrobAt` API; our lemma is the `𝓞 L`/`absNorm`-specialised consequence |
|  6 | 1-categorical → higher-categorical?                                                             | no       | classical Galois theory                                                                   | — |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary additive/monoid structure?                                     | no       | `m : ℕ`, the norm `N𝔭 : ℕ` are intrinsic                                                  | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no — and the relevant abstraction already exists in mathlib** as
`AlgHom.IsArithFrobAt.apply_of_pow_eq_one`. The "modern, maximally-typeclass-weak" engine
(`φ ζ = ζ ^ Nat.card (R ⧸ Q.under R)` over any domain `S` with a Frobenius at `Q`) is *exactly* the
mathlib lemma our proof invokes at line 83. Our theorem is the concrete number-field reading of it,
substituting `Nat.card (𝓞 K ⧸ 𝔓.under) = Ideal.absNorm 𝔭`. There is no contemporary mathlib
formulation we'd want *instead* of the current one — the contemporary formulation is the mathlib
engine, and we already sit directly on top of it. The only delta from mathlib is the **specialisation
arithmetic** (Phase 5/6).

One-line reason this is not a separate modernisation move: the maximally-general modern engine is
already in mathlib (`IsArithFrobAt.apply_of_pow_eq_one`); this lemma is its number-field
specialisation, not a candidate for a different idiom.

---

## PHASE 4.5 — Diamond / defeq risk

n/a — declaration kind is **theorem** (introduces no definitional equality or typeclass-search path).

---

## PHASE 5 — Mathlib search

### Mathlib search-status: `Chebotarev.cyclotomic_frobenius_acts_as_norm_power`

[A] Lean-Finder       n/a: AI search UI not available in this environment (recorded n/a, not blank).
[B] Loogle (`lean_loogle`)  Type-pattern intent `(σ : L ≃ₐ[K] L) → ζ ∈ primitiveRoots _ _ → σ ζ = ζ ^ Ideal.absNorm _`. MCP loogle not loadable here (ToolSearch returned none) — substituted by authoritative grep of the pinned mathlib source (method D).
[C] LeanSearch (`lean_leansearch`)  n/a: MCP tool unavailable; covered by D + the literature concept-name search (Phase 3).
[D] Grep mathlib src  Searched, across the pinned `.lake/packages/mathlib`:
                      • `apply_of_pow_eq_one`, `IsArithFrobAt`, `arithFrobAt` in `RingTheory/`;
                      • `Frobenius` ∧ `cyclotomic` ∧ `norm` across `NumberTheory/Cyclotomic/` and
                        `NumberTheory/NumberField/Cyclotomic/`;
                      • `ζ ^ .*absNorm`, `arithFrobAt.*primitiveRoots`, `primitiveRoots.*Frob`
                        repo-wide (mathlib); `absNorm.*Coprime` in `NumberTheory/`.
                      → KEY HITS:
                        • `Mathlib/RingTheory/Frobenius.lean:109`
                          **`AlgHom.IsArithFrobAt.apply_of_pow_eq_one`** — for a domain `S`, a
                          Frobenius `φ : S →ₐ[R] S` at `Q`, an `m`-th root of unity `ζ` with
                          `↑m ∉ Q`: `φ ζ = ζ ^ Nat.card (R ⧸ Q.under R)`. ← **the element-level
                          engine; our proof calls this directly at line 83.**
                        • `Mathlib/NumberTheory/NumberField/Cyclotomic/Galois.lean:63`
                          `IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq` — for `K = ℚ`,
                          `σ x = x ^ (galEquivZMod n K σ).val.val` when `x^n = 1`. The `ℚ`-only
                          analog, phrased via the cyclotomic-character *value* (not via `absNorm`,
                          and not via a Frobenius at a prime). Its companion line-70
                          `galEquivZMod_smul_of_pow_eq` is the `𝓞 K` version.
                        • Same file `:113` `mem_zpowers_galEquivZMod_of_mem_stabilizer` and `:136`
                          `galEquivZMod_stabilizer` — the `ℚ`-only **decomposition-group** form
                          (image of `D_𝔓` = `zpowers (ZMod.unitOfCoprime p hn)`). Its proof is the
                          `ℚ`-analog of *this lemma + its sibling*, but it **inlines** the
                          `ζ ↦ ζ^{Np}` step through `galEquivZMod_smul_of_pow_eq` + `Int.card_ideal_quot`
                          — it never exposes a reusable `Frob_𝔭(ζ) = ζ^{N𝔭}` statement.
                        • `Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean` —
                          `modularCyclotomicCharacter`/`IsPrimitiveRoot.autToPow_spec`: the abstract
                          cyclotomic character `g(ζ) = ζ^{c(g)}`. NO Frobenius/prime/norm content.
[E] Name pattern (`lean_local_search`)  n/a: local search tool unavailable + project build stale;
                      substituted by repo-wide grep — `arithFrobAt`/`IsArithFrobAt`/`apply_of_pow_eq_one`
                      ARE mathlib (`RingTheory/Frobenius.lean`); `UnramifiedIn`/`primitiveRoots`-as-set
                      glue is project-local.

Searched for both:
  - the user's current form (general base `K`, `Frob_𝔓(ζ) = ζ^{absNorm 𝔭}`): **not present** — no
    mathlib lemma states the Frobenius action on a root of unity with exponent `Ideal.absNorm`.
    (`grep "ζ ^ .*absNorm"` over mathlib returns nothing.)
  - the literature-standard / `ℚ`-special / abstract forms: mathlib has (i) the **abstract engine**
    `AlgHom.IsArithFrobAt.apply_of_pow_eq_one` with exponent `Nat.card (R ⧸ Q.under R)`, and
    (ii) the **`ℚ`-only** character-value form `galEquivZMod_apply_of_pow_eq` and the `ℚ`-only
    decomposition-group form `galEquivZMod_stabilizer`. It does **not** have the general-base
    number-field statement with exponent `absNorm`, on the `arithFrobAt` Frobenius.

Concluded: **found the building block in mathlib** — `AlgHom.IsArithFrobAt.apply_of_pow_eq_one`
(`RingTheory/Frobenius.lean:109`) is the element-level engine; our theorem is its number-field
specialisation, obtained by (a) instantiating at the genuine Frobenius `arithFrobAt (𝓞 K) Gal(L/K) 𝔓`,
(b) discharging `(m : 𝓞 L) ∉ 𝔓` from `hcop`, (c) rewriting `Nat.card (𝓞 K ⧸ 𝔓.under) = Ideal.absNorm 𝔭`,
and (d) pushing along `algebraMap (𝓞 L) L` to land in `L`. The *general-base packaged form* is absent
from mathlib, but the mathematical core is a mathlib lemma we already call.

---

## PHASE 6 — Composition check (+ call-sites)

### Call sites — `Chebotarev.cyclotomic_frobenius_acts_as_norm_power`

Internal use count (within the project, **excluding** the declaring file): **0**.
External-to-file callers: **0** (the mention at `ZetaProduct.lean:1770` is a docstring/comment, not
a call site).
Use within the declaring file: **1** — `CyclotomicNormResidue.lean:119`, inside
`autToPow_frobeniusClass_out` (`hact : φ ζ = ζ ^ Ideal.absNorm 𝔭 := cyclotomic_frobenius_acts_as_norm_power …`).

| Caller file:line                 | Usage pattern (one-line excerpt)                                                            |
|----------------------------------|---------------------------------------------------------------------------------------------|
| `CyclotomicNormResidue.lean:119` | `have hact : φ ζ = ζ ^ Ideal.absNorm 𝔭 := cyclotomic_frobenius_acts_as_norm_power K L m 𝔭 hunr hcop 𝔓 h𝔓lo ζ …` — feeds the element equality into the character-form proof in the **same file** |

(`ZetaProduct.lean:1770` is a comment describing the role; not a call.)

Inline-derivation grep (was the equivalent re-derived elsewhere without using this lemma?):
  - (none in the project) — the only place `Frob(ζ) = ζ^{N𝔭}` is needed is `autToPow_frobeniusClass_out`,
    which goes through this lemma. **In mathlib, however**, the `ℚ`-analog
    `mem_zpowers_galEquivZMod_of_mem_stabilizer` re-derives the same `ζ ↦ ζ^{Np}` step inline (via
    `galEquivZMod_smul_of_pow_eq` + `Int.card_ideal_quot`) rather than through a reusable lemma — i.e.
    even mathlib currently lacks a packaged `Frob_𝔭(ζ) = ζ^{N𝔭}` and inlines it.

**Signal:** K = 0 external uses; the lemma's sole consumer is the sibling theorem in the same file.
Per the call-sites table, "K = 1 internal use only ⇒ possibly the wrong abstraction — could be
inlined" applies here (the one use is even *intra-file*). This is the file-internal factoring of a
single shared step (this element form + its character repackaging), reasonable as project structure,
but it pulls the verdict away from "independent reusable API" and toward "specialisation / inlinable".

### Composition check (Phase 6)

Can `cyclotomic_frobenius_acts_as_norm_power` be derived from mathlib in ≤3 chained calls?

Attempt 1 — directly off the mathlib engine `AlgHom.IsArithFrobAt.apply_of_pow_eq_one`.
Sketch (the actual structure of the project's proof, with mathlib decls named):
```lean
-- with z := hζ.toInteger : 𝓞 L,  hzpow : z ^ m = 1,  hmnotmem : (m : 𝓞 L) ∉ 𝔓
have key : (arithFrobAt (𝓞 K) Gal(L/K) 𝔓) • z = z ^ Nat.card (𝓞 K ⧸ 𝔓.under (𝓞 K)) :=
  (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓).apply_of_pow_eq_one hzpow hmnotmem   -- mathlib
-- rewrite Nat.card (𝓞 K ⧸ 𝔓.under) = Ideal.absNorm 𝔭     (Ideal.LiesOver.over + absNorm_apply, mathlib)
-- push along algebraMap (𝓞 L) L                            (map_pow, mathlib)
```
  - Mathlib decls used: `AlgHom.IsArithFrobAt.apply_of_pow_eq_one`, `IsArithFrobAt.arithFrobAt`,
    `Ideal.absNorm_apply` / `Submodule.cardQuot_apply`, `Ideal.LiesOver.over`, `map_pow`.
  - Result: **partial.** The *mathematical* heart is one mathlib call (`apply_of_pow_eq_one`), but
    turning it into the stated conclusion is **not** a ≤3-call chain. It needs genuine glue: (i)
    construct `z = hζ.toInteger` and `z^m = 1` from `ζ ∈ primitiveRoots m L`
    (`mem_primitiveRoots`, `IsPrimitiveRoot.toInteger`, `…toInteger_isPrimitiveRoot.pow_eq_one`);
    (ii) prove `(m : 𝓞 L) ∉ 𝔓` — an **~8-line sub-argument** using `absNorm_span_singleton`,
    `Algebra.norm_algebraMap`, `Int.natAbs_pow`, the coprimality `hcopP` lifted from `hcop` via
    `absNorm_eq_pow_inertiaDeg_of_liesOver`, and `Nat.Coprime.eq_one_of_dvd`; (iii) the
    `Nat.card = absNorm` rewrite (`hqcard`); (iv) transport `(𝓞 L)`-equality → `L`-equality along
    the algebra map, including the `MulSemiringAction.toAlgHom … = φ ζ` defeq bridge.

Attempt 2 — off the `ℚ`-only mathlib hits (`galEquivZMod_apply_of_pow_eq` / `galEquivZMod_stabilizer`).
  - Result: **fails.** Those are `K = ℚ`-hardcoded (namespace `IsCyclotomicExtension.Rat`); they give
    nothing for general base `K`, and are phrased via the cyclotomic-character *value*, not via the
    arithmetic Frobenius at `𝔓` with exponent `absNorm`. Not a composition for our statement.

Conclusion: **NOT-COMPOSABLE as a ≤3-call chain.** The mathematical core is a single mathlib lemma
(`apply_of_pow_eq_one`), but the user's *stated form* requires a genuine multi-step wrapper
(primitive-root bookkeeping, the `(m:𝓞 L) ∉ 𝔓` sub-proof, the `Nat.card ↔ absNorm` identification,
and the `𝓞 L → L` transport). It is more than 3 calls — it is a real ~25-line proof — but it is
*shallow*: every step is mathlib-provided, with only project-local glue (`UnramifiedIn`,
`arithFrobAt` instances) and no new mathematical idea beyond the mathlib engine.

---

## Verdict: `Chebotarev.cyclotomic_frobenius_acts_as_norm_power`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature search (Phase 3): classical, standard, general-base element form
  `Frob_𝔭(ζ) = ζ^{N𝔭}`; named (Artin/cyclotomic Frobenius formula); Sharifi §7.2 (cited source),
  Conrad, Washington. No dispute on the form.
- Generality analysis (Phase 4): MAXIMALLY GENERAL (general base field — strictly more general than
  mathlib's `ℚ`-only counterpart); 0 genuine weakenings; **the modern maximally-general engine
  already exists in mathlib** (`apply_of_pow_eq_one`) and this lemma sits directly on it (Phase 4c).
- Mathlib search (Phase 5): the **building block IS in mathlib** —
  `AlgHom.IsArithFrobAt.apply_of_pow_eq_one` (`RingTheory/Frobenius.lean:109`), called directly by
  the proof. The *packaged* general-base form with exponent `absNorm` is absent; the only adjacent
  packaged results are `ℚ`-only (`galEquivZMod_apply_of_pow_eq`, `galEquivZMod_stabilizer`).
- Composition check (Phase 6): NOT-COMPOSABLE as a ≤3-call chain, but the proof is a *shallow*
  ~25-line wrapper over the mathlib engine; **K = 0 external call sites** (sole consumer is the
  sibling theorem in the same file).

**Rationale (why BORDERLINE rather than a clean verdict):**

This lemma is genuinely on the fence, and the tension is explicit. On one side, the *mathematical
content* is classical and the *packaged general-base form is not in mathlib* — mathlib's only
cyclotomic-Frobenius-on-roots-of-unity results are `ℚ`-hardcoded (`IsCyclotomicExtension.Rat.*` in
the 2026 Roblot file `NumberField/Cyclotomic/Galois.lean`), and even those inline the `ζ ↦ ζ^{Np}`
step rather than exposing a reusable `Frob_𝔭(ζ) = ζ^{N𝔭}`. That argues for a YES (the
general-number-field element form is a real, absent, standard statement). On the other side, three
facts pull hard toward NO-composable: (1) the entire mathematical core is a single existing mathlib
lemma, `AlgHom.IsArithFrobAt.apply_of_pow_eq_one`, which the proof calls directly — everything else
is bookkeeping (build the root of unity, discharge `(m:𝓞 L)∉𝔓` from `hcop`, identify
`Nat.card(𝓞K/𝔓.under) = absNorm 𝔭`, transport `𝓞 L → L`); (2) it is **not composable in ≤3 calls**
only because of that glue, not because of any new idea — so it falls in the awkward gap between
"trivially inlinable" and "novel lemma"; (3) it has **zero external call sites** — its sole consumer
is the sibling `autToPow_frobeniusClass_out` *in the same file*, so as it stands it is a file-internal
factoring of one shared step, not independent reusable API.

What turns this from a mechanical call into a human decision is *which* of two reasonable
upstreaming stories mathlib wants — and that is a packaging judgment, identical in shape to the one
flagged for the sibling `autToPow_frobeniusClass_out`. **Story A (YES-but-generalise-first):** mathlib
*should* have a packaged number-field corollary of `apply_of_pow_eq_one` — namely
`arithFrobAt … 𝔓 ζ = ζ ^ Ideal.absNorm 𝔭` for `𝔓 ∣ 𝔭` in a number field — sitting next to
`absNorm_eq_pow_inertiaDeg_of_liesOver`, and the right contribution is to add it (restated on mathlib
idioms: drop the project-local `UnramifiedIn` in favour of `𝔓.LiesOver 𝔭` + `(absNorm 𝔭).Coprime m`,
which is all the proof actually uses). This would also be the clean general-base lemma from which the
`ℚ`-only `mem_zpowers_galEquivZMod_of_mem_stabilizer` proof could be refactored. **Story B
(NO-composable-from-mathlib):** the "lemma" is just `apply_of_pow_eq_one` plus four lines of
specialisation glue with no independent consumers, so mathlib should simply expect users to call
`apply_of_pow_eq_one` directly and do the `Nat.card ↔ absNorm` rewrite inline at the (one) call site —
no new mathlib lemma. The honest call between A and B depends on (i) whether mathlib wants the
number-field `absNorm`-exponent packaging as first-class API (a taste/policy call), and (ii)
coordination with the active 2026 `Cyclotomic/Galois.lean` development, where such a lemma would most
naturally live. The skill cannot make that call alone; hence BORDERLINE. (Note: the deciding factor is
*packaging/coordination*, not cost — so this is a genuine BORDERLINE, not a cost-driven downgrade.)

**Numbered questions for the user (≤5):**

  1. Does mathlib want a **packaged number-field corollary** of `AlgHom.IsArithFrobAt.apply_of_pow_eq_one`,
     namely `arithFrobAt (𝓞 K) Gal(L/K) 𝔓 ζ = ζ ^ Ideal.absNorm 𝔭` (for `𝔓 ∣ 𝔭`, `ζ` a primitive
     `m`-th root, `(N𝔭).Coprime m`), as first-class API — or should users just call
     `apply_of_pow_eq_one` and inline the `Nat.card (𝓞 K ⧸ 𝔓.under) = absNorm 𝔭` rewrite (the
     NO-composable resolution)?
  2. If YES to (1): should it be contributed into / coordinated with the 2026
     `Mathlib/NumberTheory/NumberField/Cyclotomic/Galois.lean` (Roblot), as the **general-base
     element lemma** underlying the existing `ℚ`-only `galEquivZMod_apply_of_pow_eq` /
     `mem_zpowers_galEquivZMod_of_mem_stabilizer` — i.e. lift those from `ℚ` to general `K`?
  3. For the mathlib restatement, is it acceptable to **drop the project-local `UnramifiedIn 𝔭`
     hypothesis** (the element proof uses only `𝔓.LiesOver 𝔭`, `(N𝔭).Coprime m`, and `Finite (𝓞 L⧸𝔓)`),
     stating it purely on mathlib idioms — or should it keep an unramified/finite-residue hypothesis
     for uniqueness-API parity?
  4. Should this **element-level** lemma be upstreamed and the sibling **character-level**
     `autToPow_frobeniusClass_out` derived from it (the natural dependency order), or are the two
     assessed/contributed together as one PR?
  5. Given **zero external call sites** (sole consumer is the same-file sibling), is the
     general-base element form worth shipping to mathlib on its own merits (standard + currently
     absent), or only as a refactor of the existing `ℚ`-only `Galois.lean` proofs?

**Next action:** user answers the five questions (chiefly Q1: package vs inline, and Q2:
coordinate with the 2026 `Cyclotomic/Galois.lean`). Then either (a) **NO-composable-from-mathlib** —
inline `apply_of_pow_eq_one` at the one call site and delete this wrapper; or (b)
**YES-but-generalise-first** — restate on mathlib idioms (drop `UnramifiedIn`, key on
`𝔓.LiesOver 𝔭` + coprimality) and contribute as the general-base element lemma underlying
`NumberField/Cyclotomic/Galois.lean`, then run `/generalise`.

---

## Next step

User answers the five numbered questions above (package-as-API vs inline; coordination with the 2026
`NumberField/Cyclotomic/Galois.lean`; whether to drop the project-local `UnramifiedIn` for mathlib
idioms; element-before-character upstreaming order; whether zero-external-use changes the calculus).
The mathematical content is standard and the packaged general-base form is absent from mathlib, but
its entire core is the existing `AlgHom.IsArithFrobAt.apply_of_pow_eq_one` plus specialisation glue
with no external consumers — so whether it becomes a mathlib lemma (Story A) or is inlined at its one
call site (Story B) is a packaging/coordination decision a human must make.
