# /mathlibable report — `Chebotarev.autToPow_frobeniusClass_out`

## Baseline (Phase 0)

- lake build:               not run (local build known stale per task; reasoned from source — the
                            decl elaborates as written, all referents resolve in the repo)
- decl `Chebotarev.autToPow_frobeniusClass_out`: ✓ resolved at
                            `projects/Chebotarev/CebotarevDensity/CyclotomicNormResidue.lean:100`
- qualified name:           `Chebotarev.autToPow_frobeniusClass_out`
                            (`namespace Chebotarev` opens at line 36; no nested namespace; theorem at 100)
- kind:                     theorem
- has sorry:                no
- module docstring summary: "The cyclotomic Frobenius as a norm residue, and Frobenii generate" —
                            two arithmetic inputs to the Frobenius-fibre equidistribution, placed
                            below `ZetaProduct.lean` in the import order.

---

## Statement (Phase 1)

`Chebotarev.autToPow_frobeniusClass_out` is a **theorem** stating the following.

Let `K` be a number field, `m ≥ 1` an integer, and `L = K(μ_m)` the `m`-th cyclotomic extension
(`IsCyclotomicExtension {m} K L`, `IsGalois K L`). Let `ζ ∈ L` be a primitive `m`-th root of unity.
Let `𝔭` be a prime ideal of `O_K` that is **unramified in `L`** and whose **absolute norm `N𝔭` is
coprime to `m`**. Then the **cyclotomic character** `IsPrimitiveRoot.autToPow`
(the faithful monoid hom `Gal(L/K) →* (ℤ/mℤ)ˣ` sending an automorphism to the power it raises
`ζ` to) sends the **Frobenius representative** `(frobeniusClass K L 𝔭).out` to the unit
`N𝔭 mod m`:

  `hζ.autToPow K ((frobeniusClass K L 𝔭).out) = ZMod.unitOfCoprime (Ideal.absNorm 𝔭) hcop`.

This is the multiplicative-character form of the element-level fact `Frob_𝔭(ζ) = ζ^{N𝔭}`
(the project's `cyclotomic_frobenius_acts_as_norm_power`, Sharifi 7.2.1(i) / Prop. 7.1.15-adjacent).

Variables / typeclasses (Lean side):
- `K L : Type*`, `[Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]` —
  the number-field cyclotomic extension `L/K`.
- `m : ℕ`, `[NeZero m]`, `[IsCyclotomicExtension {m} K L]` — `L = K(μ_m)`.
- `{ζ : L} (hζ : IsPrimitiveRoot ζ m)` — a chosen primitive `m`-th root of unity.
- `(𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime]` — the prime of the base.

Hypotheses (Lean side):
- `hunr : UnramifiedIn K L 𝔭` — `𝔭` is unramified in `L` (project-local predicate).
- `hcop : (Ideal.absNorm 𝔭).Coprime m` — the residue characteristic does not divide `m`.

Conclusion (math): the cyclotomic character evaluated at the Frobenius of `𝔭` equals the
norm residue `N𝔭 mod m ∈ (ℤ/mℤ)ˣ`.

Conclusion (Lean):
`hζ.autToPow K ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) = ZMod.unitOfCoprime (Ideal.absNorm 𝔭) hcop`.

---

## Size classification (Phase 2a)

Verdict: **BIG** (borderline BIG/SMALL — recorded BIG for framing).
Reason: It is a named arithmetic theorem (the cyclotomic Frobenius = norm residue, attached to
Artin reciprocity / Sharifi §7.2) and is a load-bearing arithmetic input of the project's main
Chebotarev-density development — not a one-step helper. Literature width is EXHAUSTIVE regardless.

## One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure` — one-liner check is **n/a**. (The proof body
is ~25 substantive lines: obtain a prime `𝔓` above `𝔭`, build the arithmetic Frobenius `φ`, show
the Frobenius class is `mk φ`, transport along conjugacy via `autToPow.map_isConj`, apply the
element-level `cyclotomic_frobenius_acts_as_norm_power`, then convert the exponent equality to a
`ZMod` unit equality via `autToPow_spec` and `pow_natModEq_of_pow_eq`.)

---

## PHASE 3 — Literature search (EXHAUSTIVE)

### Literature search table

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found                                                                 | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|--------------------------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "cyclotomic character Frobenius prime norm residue Gal(K(ζ_m)/K) sends Frobenius to N(p) mod m" | yes  | `χ(Frob_𝔭) = N𝔭 mod m`; `Gal(ℚ(ζ_m)/ℚ) ≅ (ℤ/m)ˣ`                                     | Hits incl. Sharifi `cycl.pdf` (the project's cited source), Wiese GalRep notes, Erickson Cyclotomic Fields III |
|  2 | WebSearch (general/named form)   | "Frobenius automorphism cyclotomic field acts as ζ^{norm power} number field standard theorem" | yes  | Artin automorphism: `ζ_m ↦ ζ_m^ℓ`; over number fields via norm                       | Confirms the Artin/Frobenius automorphism is the standard name; the `ζ ↦ ζ^{Np}` form is textbook |
|  3 | WebSearch (Artin-map alias, general base) | "Artin map cyclotomic extension number field Frobenius prime ideal norm residue (O_K/m)^× general base field" | yes | Artin map description: decomposition group ≅ Gal of residue extension, canonical Frobenius; every abelian ext of `K` lies in a cyclotomic field | MIT 18.785 Lecture 7 & 21; Climbing Mount Bourbaki "Artin map on ideals"; general base field is standard |
|  4 | ChatGPT MCP                      | (standard name + generality + CFT-free vs Artin-map; idiomatic Lean form)                       | n/a  | —                                                                                    | **MCP down** (Codex exec failed twice — matches the task's "ChatGPT MCP may be down" warning); compensated by extra WebSearch + Wikipedia channels |
|  5 | Local references                 | grep `.mathlib-quality/references/` for "cyclotomic"/"Frobenius"                                | n/a  | (no `references/` dir in this project)                                                | Directory absent — recorded n/a. Docstrings cite Sharifi §7.2 / Prop. 7.1.15, the `cycl.pdf` that surfaced in channel 1 |
|  6 | nLab                             | "cyclotomic character Frobenius norm prime roots of unity Galois"                               | partial | cyclotomic character = Galois action on roots of unity; `χ_p(Frob_ℓ)=ℓ` over ℚ      | nLab page itself not surfaced; Wikipedia "Cyclotomic character" gives the canonical `χ_p(Frob_ℓ)=ℓ` (ℚ-level) |
|  7 | nCatLab (if categorical)         | —                                                                                              | n/a  | not a categorical concept                                                             | This is arithmetic Galois theory, no higher-categorical content |
|  8 | Stacks Project (if alg geom)     | —                                                                                              | n/a  | not a scheme-theoretic statement                                                      | Number-field Frobenius / cyclotomic character; outside Stacks' scope |
|  9 | MathOverflow / Math.StackExchange| (covered transitively by channels 1–3 hits: REU notes, lecture notes)                          | yes  | same `ζ ↦ ζ^{Np}` / `χ(Frob)=N𝔭` consensus                                          | Park "Existence of the Frobenius element", Meli "Cyclotomic ext & quadratic reciprocity" corroborate |
| 10 | recent arXiv (last 5 years)      | (surfaced in channels 1–2: arXiv 1511.01755, 2207.13911)                                        | yes  | uses the identity as standard background                                              | Not a novel/recent result — it is classical bedrock |

Wikipedia "Cyclotomic character" (fetched): *"If Frob_ℓ is a Frobenius element for ℓ ≠ p, then
χ_p(Frob_ℓ) = ℓ."* — the ℚ-level statement; the article does not treat general number fields or
`N𝔭 mod m`.

### Literature summary (Phase 3)

Concept identified as: **the cyclotomic / Artin–Frobenius automorphism formula** — `Frob_𝔭(ζ) = ζ^{N𝔭}`,
equivalently *the cyclotomic character sends the Frobenius of `𝔭` to the norm residue `N𝔭 mod m`*.
The `K = ℚ` shadow is the canonical isomorphism `(ℤ/mℤ)ˣ ≅ Gal(ℚ(ζ_m)/ℚ)`.

Sources agree on the standard form: **yes**. It is classical bedrock of algebraic number theory
(Washington *Cyclotomic Fields*; Sharifi notes §7.2; MIT 18.785; every CFT course).

Most general standard form: an **arbitrary number-field base `K`**, `L = K(μ_m)`, `𝔭` unramified
with `N𝔭` coprime to `m`. The general base field is standard (it is the cyclotomic case of the
Artin map; "every abelian extension of `K` lies in a cyclotomic field" is stated over general `K`).

Generality dimensions where the literature varies:
  - Base field: from `ℚ` (most common pedagogical statement, giving `(ℤ/m)ˣ ≅ Gal`) to **arbitrary
    number field `K`** (the project's form — fully standard).
  - Packaging: (a) element form `Frob_𝔭(ζ) = ζ^{N𝔭}`; (b) character form `χ(Frob_𝔭) = N𝔭 mod m`;
    (c) decomposition-group form (image of `D_𝔓` is `⟨N𝔭 mod m⟩`). The project provides (b) on the
    conjugacy-class representative; mathlib provides (c) over `ℚ` only (see Phase 5).
  - Provenance: usually deduced CFT-free for the cyclotomic case (the proof here is CFT-free,
    routed through the residue-field Frobenius `φ ζ = ζ^q`), then *subsumed* by Artin reciprocity.

Disagreement with the literature: **none**. The project's form is the standard general-base-field
character form.

---

## PHASE 4 — Generality analysis

### Generality status table — `Chebotarev.autToPow_frobeniusClass_out`

Literature-standard form (Phase 3): general number field `K`, `L = K(μ_m)`, `𝔭` unramified with
`N𝔭` coprime to `m`; `χ(Frob_𝔭) = N𝔭 mod m`.

| # | Parameter / hypothesis                              | Current Lean form                  | Literature-standard form                  | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------------------------|------------------------------------|-------------------------------------------|---------------------|---------------------------------|
| 1 | `[NumberField K]` (base field)                      | arbitrary number field             | arbitrary number field                    | NO (already general)| This IS the general base; mathlib only has the `ℚ` specialisation. Not narrower than standard. |
| 2 | `[IsCyclotomicExtension {m} K L]`                    | `L = K(μ_m)`                       | `L = K(μ_m)`                              | NO                  | Intrinsic to the cyclotomic statement. |
| 3 | `(hunr : UnramifiedIn K L 𝔭)`                       | unramified in `L`                  | unramified (equiv. `𝔭 ∤ m` for nontrivial ext) | NO              | Necessary; ramified primes have no single Frobenius. Standard hypothesis. |
| 4 | `(hcop : (Ideal.absNorm 𝔭).Coprime m)`              | `N𝔭` coprime to `m`                | `N𝔭` coprime to `m` (residue char ∤ m)    | NO                  | Necessary for `ZMod.unitOfCoprime` to make sense and for `ζ` to stay primitive mod `𝔓`. |
| 5 | `{ζ} (hζ : IsPrimitiveRoot ζ m)` + `autToPow`       | character via a chosen `ζ`         | the (ζ-independent) cyclotomic character  | marginal (idiom)    | `autToPow` depends on a chosen `ζ`; a ζ-independent `modularCyclotomicCharacter`-style statement is an *idiom* alternative — see 4c. Not a generality weakening. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (in the literature-generality sense). The base field is
already an arbitrary number field — strictly *more* general than mathlib's `ℚ`-only counterpart
(Phase 5). No hypothesis is stronger than the literature-standard cluster; all four hypotheses are
the standard, necessary ones.

Number of weakening opportunities found: **0** (one idiom-reformulation candidate, row 5 → Phase 4c).
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                       | Applies? | Proposed reformulation                                                                 | Mathlib downstream this enables |
|----|------------------------------------------------------------------------------------------------|----------|-----------------------------------------------------------------------------------------|---------------------------------|
|  1 | "let X be a foo" preambles → typeclasses?                                                       | no       | already fully typeclass-driven (`IsCyclotomicExtension`, `IsGalois`, `NumberField`)     | — |
|  2 | sequences/metric → filters/topological?                                                         | no       | finite/arithmetic statement; no limit content                                           | — |
|  3 | construct an object where a universal property would characterise it?                           | no       | it is a *theorem* (an equality of units), not a construction                            | — |
|  4 | set-with-closure-predicate → bundled substructure?                                              | no       | no substructure here                                                                    | — |
|  5 | vector-space/metric/field-specific → weaker typeclass?                                          | partial  | the *base field* is already maximally weak for the arithmetic setting (number field); the element-engine is even stated by mathlib over a general Frobenius `IsArithFrobAt` (see `RingTheory/Frobenius.lean`) | the general-base-field statement is itself the modernisation of mathlib's `ℚ`-only `galEquivZMod_stabilizer` |
|  6 | 1-categorical → higher-categorical?                                                             | no       | classical Galois theory                                                                  | — |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary additive/monoid structure?                                     | no       | `m : ℕ`, `(ℤ/mℤ)ˣ` are intrinsic to the cyclotomic statement                            | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **partial / minor** — the only candidate is whether to state the result
against the ζ-independent `modularCyclotomicCharacter L m` (the `RingEquiv`-based cyclotomic
character mathlib also has) instead of `IsPrimitiveRoot.autToPow` (which is keyed to a chosen `ζ`).
This is a *formulation* choice, not a real organisational improvement — both characters are in
mathlib and `autToPow` is the standard `AlgEquiv` form already used by mathlib's own `galEquivZMod`.
The substantive "modernisation" here is exactly the **general-base-field generalisation** of
mathlib's `ℚ`-only result (`IsCyclotomicExtension.Rat.galEquivZMod_stabilizer`), which is captured
in Phase 5 / Phase 7, not as a 4c idiom swap.

One-line reason this is not a separate modernisation move: the result is already stated with
contemporary mathlib typeclasses at the maximal arithmetic generality; the character used is the
one mathlib itself uses for this purpose.

---

## PHASE 4.5 — Diamond / defeq risk

n/a — declaration kind is **theorem** (introduces no definitional equality or typeclass-search path).

---

## PHASE 5 — Mathlib search

### Mathlib search-status: `Chebotarev.autToPow_frobeniusClass_out`

[A] Lean-Finder       n/a: AI search UI not available in this environment (recorded n/a, not blank)
[B] Loogle (`lean_loogle`)  n/a: MCP loogle tool not loadable here (ToolSearch returned none) — substituted by exhaustive grep of the pinned mathlib source (method D), which is authoritative for "does mathlib contain this"
[C] LeanSearch (`lean_leansearch`)  n/a: same — MCP tool unavailable; covered by D + the literature concept-name search in Phase 3
[D] Grep mathlib src  Searched `autToPow` ∧ {`absNorm`,`unitOfCoprime`,`Frobenius`,`frobenius`};
                      `frobenius.*cyclotomic`/`cyclotomic.*frobenius` across `NumberTheory/`;
                      `IsArithFrobAt` / `arithFrobAt` in `RingTheory/`.
                      → KEY HITS (3 files contain `autToPow`+`unitOfCoprime`/`absNorm`):
                        • `Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.lean` — defines
                          `IsPrimitiveRoot.autToPow : (S ≃ₐ[R] S) →* (ZMod n)ˣ` and the abstract
                          `autToPow_spec : μ ^ (autToPow R f).val = f μ`. (The character + its spec,
                          NO Frobenius/norm content.)
                        • `Mathlib/NumberTheory/Cyclotomic/Gal.lean` — `autToPow_injective`,
                          `autEquivPow`, `fromZetaAut`. (Galois-group structure, NO Frobenius/norm.)
                        • `Mathlib/NumberTheory/NumberField/Cyclotomic/Galois.lean` (Roblot, ©2026)
                          — `IsCyclotomicExtension.Rat.galEquivZMod_stabilizer` and helper
                          `mem_zpowers_galEquivZMod_of_mem_stabilizer`: for `K = ℚ`, `p ∤ n`, the
                          image of the decomposition group of `P|p` under `galEquivZMod` is
                          `Subgroup.zpowers (ZMod.unitOfCoprime p hn)`. ← the closest analog.
                        • `Mathlib/RingTheory/Frobenius.lean` — `IsArithFrobAt.apply_of_pow_eq_one`:
                          for an abstract Frobenius `φ` at `Q`, `φ ζ = ζ ^ Nat.card (R ⧸ Q.under R)`
                          when `ζ^m = 1`, `↑m ∉ Q`. ← the element-level engine (a building block).
[E] Name pattern (`lean_local_search`)  n/a: local search tool unavailable + project build stale;
                      substituted by repo-wide grep — `frobeniusClass`/`UnramifiedIn` are
                      **project-local** (no mathlib def), `arithFrobAt`/`IsArithFrobAt` ARE mathlib.

Searched for both:
  - the user's current form (general base `K`, character-on-Frobenius-class): **not present**.
  - the literature-standard / `ℚ`-special form: mathlib has the **decomposition-group (zpowers)**
    version over `ℚ` only (`galEquivZMod_stabilizer`), and the abstract element-engine
    (`IsArithFrobAt.apply_of_pow_eq_one`). It does **not** have the *equality*
    `χ(Frob) = N𝔭 mod m` (vs. membership in `zpowers`), and does **not** have any general-base-`K`
    cyclotomic-Frobenius statement (no general-base hits outside the `IsCyclotomicExtension.Rat`
    namespace).

Concluded: **not in mathlib** (all available methods exhausted, including the literature-standard
form). Mathlib has (i) the cyclotomic character `autToPow` + abstract `autToPow_spec`, (ii) the
abstract residue-field Frobenius power law `IsArithFrobAt.apply_of_pow_eq_one`, and (iii) the
`ℚ`-only decomposition-group statement `galEquivZMod_stabilizer`. The packaged general-base-field
equality `χ(Frob_𝔭) = N𝔭 mod m` on the Frobenius-class representative is absent.

---

## PHASE 6 — Composition check (+ call-sites)

### Call sites — `Chebotarev.autToPow_frobeniusClass_out`

Internal use count: **3** (within the project, excluding the declaring file).
External-to-file callers: **2 distinct files**.

| Caller file:line              | Usage pattern (one-line excerpt)                                                          |
|-------------------------------|--------------------------------------------------------------------------------------------|
| `ZetaProduct.lean:707`        | `autToPow_frobeniusClass_out K L m hζ p (unramifiedIn_of_coprime_absNorm …) hcp` (in a `rw`, to identify the per-prime norm residue, multiplied over an ideal factorisation) |
| `ZetaProduct.lean:1056`       | `rw [hH, Subgroup.mem_comap, autToPow_frobeniusClass_out K L m hζ 𝔭 h𝔭unr h𝔭cop]` (realise a residue in the image of the cyclotomic character as a prime norm residue) |
| `Main.lean:342`               | `have hdict := autToPow_frobeniusClass_out ℚ L n hζ 𝔭 hunr hcop` (the dictionary "Frob class = mk σ ↔ N𝔭 ≡ a [n]", specialised to `K = ℚ`) |

(Plus several docstring/comment mentions at `ZetaProduct.lean:598,676,1011,1043` and
`Main.lean:331` describing the role — not call sites.)

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?):
  - (none) — every consumer goes through this lemma; no site re-derives `χ(Frob) = N𝔭` inline.

**Signal:** K = 3 internal uses across 2 files, no inline re-derivation → **real API; consumers
depend on it** → leans YES.

### Composition check (Phase 6)

Can `autToPow_frobeniusClass_out` be derived from mathlib in ≤3 chained calls?

Attempt 1: `IsCyclotomicExtension.Rat.galEquivZMod_stabilizer` (the closest mathlib hit).
  - Result: **fails.** (a) It is `K = ℚ`-only (namespace `IsCyclotomicExtension.Rat`, base `ℚ`
    hardcoded) — gives nothing for general base `K`. (b) It is a *subgroup membership* /
    `zpowers` statement (`image of D_𝔓 = ⟨N𝔭 mod m⟩`), not the *equality* on a Frobenius-class
    representative this lemma asserts. (c) It uses `galEquivZMod` (the `≃*` over ℚ), not
    `IsPrimitiveRoot.autToPow` applied to `(frobeniusClass K L 𝔭).out`, nor the project's
    `frobeniusClass`. Bridging (a)–(c) is not a 1–3-call composition; (a) alone is unrecoverable.

Attempt 2: assemble from the element-engine + character spec directly.
  - Building blocks: `IsArithFrobAt.apply_of_pow_eq_one` (mathlib), `IsPrimitiveRoot.autToPow_spec`
    (mathlib), `(autToPow K).map_isConj` (mathlib), `ZMod.unitOfCoprime` API (mathlib) — PLUS the
    **project-local** `frobeniusClass`, `frobeniusClass_eq_mk_of_isArithFrobAt`, `UnramifiedIn.*`,
    and the separately-proved `cyclotomic_frobenius_acts_as_norm_power`.
  - Result: **fails as a ≤3-call composition.** The actual proof is ~25 lines: it must (1) pick a
    prime `𝔓 | 𝔭`, (2) build the arithmetic Frobenius `φ`, (3) prove `frobeniusClass = mk φ`, (4)
    extract `IsConj (frobeniusClass.out) φ` and push it through `autToPow.map_isConj` +
    `isConj_iff_eq`, (5) feed in `cyclotomic_frobenius_acts_as_norm_power` (itself a wrapper of the
    mathlib engine that handles `𝔓.under = 𝔭`, `Nat.card` vs `absNorm`, and `(m:𝓞 L) ∉ 𝔓`), then
    (6) convert the `ζ`-exponent equality to a `ZMod m` unit equality via `autToPow_spec`,
    `pow_natModEq_of_pow_eq`, and `ZMod.natCast_eq_natCast_iff`. This is a genuine proof with
    project-local glue, not a chain of `.trans`/`.symm`/one-call applications.

Conclusion: **NOT-COMPOSABLE** (from mathlib alone; the composition essentially needs the
project's own `frobeniusClass` def + the `cyclotomic_frobenius_acts_as_norm_power` wrapper, neither
of which is in mathlib).

---

## Verdict: `Chebotarev.autToPow_frobeniusClass_out`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature search (Phase 3): classical, standard, general-base-field; named the Artin/cyclotomic
  Frobenius formula; mathlib's own analog is `ℚ`-only and added recently (Roblot, ©2026).
- Generality analysis (Phase 4): MAXIMALLY GENERAL (general base field — strictly more general than
  mathlib's `ℚ`-only counterpart); 0 weakening opportunities; no real 4c modernisation beyond the
  base-field generalisation itself.
- Mathlib search (Phase 5): NOT in mathlib. Closest: `IsCyclotomicExtension.Rat.galEquivZMod_stabilizer`
  (ℚ-only, decomposition-group/`zpowers` form) + the abstract engine `IsArithFrobAt.apply_of_pow_eq_one`.
- Composition check (Phase 6): NOT-COMPOSABLE from mathlib (the proof needs the project-local
  `frobeniusClass` and the `cyclotomic_frobenius_acts_as_norm_power` wrapper); K = 3 real call sites.

**Rationale (why BORDERLINE rather than a clean YES):**

The *mathematical content* clears the mathlib bar: it is a classical, named, general-base-field
theorem; mathlib lacks it (it has only the `ℚ`-restricted decomposition-group version
`galEquivZMod_stabilizer` and the abstract residue-field engine); it is not composable from
mathlib primitives in ≤3 calls; and it has three genuine internal consumers. On content alone this
would be `YES-but-generalise-first` — "generalise mathlib's `IsCyclotomicExtension.Rat.galEquivZMod_stabilizer`
from `ℚ` to a general number field, and state it as the cleaner equality `χ(Frob_𝔭) = N𝔭 mod m`."

What blocks a clean automated YES is a **packaging/dependency judgment the skill cannot make
alone**, in three parts. (1) **Project-local statement surface.** The lemma is phrased in terms of
the project's own `frobeniusClass : ConjClasses Gal(L/K)` and its `.out` representative, and the
project-local `UnramifiedIn`. To go to mathlib it must be re-pinned onto mathlib's idioms —
mathlib's `IsArithFrobAt`/`arithFrobAt` (already present), the standard `Unramified`/inertia-degree
API, and presumably stated on a chosen prime `𝔓` or as a `zpowers`/decomposition-group statement to
match the existing `galEquivZMod_stabilizer` shape — rather than on a bespoke `frobeniusClass.out`.
That is a non-mechanical restatement, and *which* target shape mathlib wants (element equality on a
`𝔓`-Frobenius vs. the existing `zpowers` membership; `autToPow` vs. `modularCyclotomicCharacter`) is
a reviewer's call. (2) **Overlap with a freshly-added mathlib file.** `NumberField/Cyclotomic/Galois.lean`
landed in 2026 and is actively being built out by Roblot; the right contribution is almost
certainly a *generalisation/extension of that file* (lift `Rat.galEquivZMod_stabilizer` to general
`K`, add the element-equality corollary), coordinated with its author — not a parallel
`Chebotarev`-namespace theorem. (3) **Necessary upstreaming of its dependency.** The proof factors
through `cyclotomic_frobenius_acts_as_norm_power` (the project's general-base-field wrapper of
`IsArithFrobAt.apply_of_pow_eq_one`, handling `𝔓.under = 𝔭`, `absNorm` vs `Nat.card`, `(m:𝓞 L) ∉ 𝔓`).
Whether to upstream *that* element-level lemma first (likely the more fundamental mathlib
contribution) and then derive the character form, vs. upstreaming the character form directly, is a
sequencing decision for a human.

None of these are "is it good math" doubts — they are "what exact statement, in whose file, on top
of which upstreamed dependency" doubts. That is precisely the BORDERLINE bucket.

**Numbered questions for the user (≤5):**

  1. Target shape: should the mathlib version be the **element/representative equality**
     `χ(Frob_𝔭) = N𝔭 mod m` (as here), or the **decomposition-group membership** form matching
     the existing `IsCyclotomicExtension.Rat.galEquivZMod_stabilizer` (image of `D_𝔓` is
     `zpowers (ZMod.unitOfCoprime …)`), generalised to a general base field `K`?
  2. Should this be contributed as a **generalisation of `Mathlib/NumberTheory/NumberField/Cyclotomic/Galois.lean`**
     (Roblot's 2026 file: lift the `Rat.` results from `ℚ` to general `K`), coordinating with its
     author — rather than as a standalone theorem?
  3. Should the underlying **`cyclotomic_frobenius_acts_as_norm_power`** (element-level, general base,
     wrapping mathlib's `IsArithFrobAt.apply_of_pow_eq_one`) be upstreamed **first** as the more
     fundamental lemma, with this character-level statement derived from it?
  4. Restating on mathlib idioms means dropping the project-local `frobeniusClass`/`.out` and
     `UnramifiedIn` in favour of a chosen prime `𝔓` + mathlib `arithFrobAt` + standard `Unramified`
     API. Is that restatement in scope now, or deferred until the project's Frobenius API
     (`frobeniusClass`, `UnramifiedIn`) is itself assessed for upstreaming?
  5. Character choice: state via `IsPrimitiveRoot.autToPow` (chosen-`ζ`, as here and as mathlib's
     `galEquivZMod` uses) or the `ζ`-independent `modularCyclotomicCharacter`?

**Next action:** user answers the five questions; then re-run `/mathlibable` (or go straight to
`/generalise` on the chosen mathlib-idiom restatement). Most likely resolution: **YES-but-generalise-first**
— upstream `cyclotomic_frobenius_acts_as_norm_power` and/or the general-base-field
`galEquivZMod_stabilizer` analog into `NumberField/Cyclotomic/Galois.lean`, with this lemma as the
character-level corollary — once the target shape (Q1) and file/coordination (Q2) are settled.

---

## Next step

User answers the five numbered questions above (target shape, host file/coordination with the 2026
`Cyclotomic/Galois.lean`, dependency-upstreaming order, project-API-restatement scope, character
choice). Re-run `/mathlibable` or `/generalise` to convert to the concrete contribution. The
content is mathlib-worthy and absent from mathlib; only the packaging/sequencing needs a human call.
