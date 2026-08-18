# /mathlibable report — `Chebotarev.character_orthogonality_cyclotomic_eq`

> Step-9 mathlibable assessment (single declaration). Local Lean build is stale, so
> Phase-0 `lake build` and the `lean_*` MCP probes were not run live; the verdict
> reasons from the source statement + proof + direct mathlib `grep` (method [D]) +
> WebSearch, as instructed. Qualified name **VERIFIED from source** (see Phase 0).
> This is the **matching-case** twin of `character_orthogonality_cyclotomic_ne`
> (same file, lines 213–225); the two share one proof skeleton (`if_pos` vs `if_neg`),
> so this report parallels the `_ne` report and is cross-checked against it.

---

### Baseline (Phase 0)
- lake build:               (not run — stale local build; reasoning from source per task brief)
- decl `Chebotarev.character_orthogonality_cyclotomic_eq`: ✓ resolved at
  `projects/Chebotarev/CebotarevDensity/Cyclotomic.lean:192`
  - `namespace Chebotarev` opens at line 49, `end Chebotarev` at line 1003 → qualified
    name is **`Chebotarev.character_orthogonality_cyclotomic_eq`** (the parsed guess was correct).
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Chebotarev's density theorem, cyclotomic case — density of primes
  of `𝓞 K` unramified in `L = K(μ_m)` with Frobenius `= σ` is `1/|Gal(L/K)|`.

---

### Statement (Phase 1)

`Chebotarev.character_orthogonality_cyclotomic_eq` is **Sharifi 7.2.1 step (iii), the
matching case** of the character-orthogonality collapse used inside the cyclotomic
Chebotarev proof. In prose:

Let `L/K` be a Galois extension of number fields with `L = K(μ_m)` (so `Gal(L/K)` is
abelian), let `σ ∈ Gal(L/K)`, and let `𝔭` be a prime of `𝓞 K` unramified in `L`. Write
`G = Gal(L/K)`, `Ĝ = (G →* ℂˣ)` for its (complex) character group, and `Frob 𝔭` for a
representative of the Frobenius conjugacy class `frobeniusClass K L 𝔭`. **If the Frobenius
class of `𝔭` *is* the class of `σ`** (`frobeniusClass K L 𝔭 = ConjClasses.mk σ`), then the
twisted character sum equals the group order:
`∑_{χ ∈ Ĝ} χ(σ) · χ(Frob 𝔭)⁻¹ = |G|`.

This is one half of the standard orthogonality dichotomy `∑_χ χ(σ)χ(τ)⁻¹ = |G|·[σ=τ]`,
specialised to `τ = Frob 𝔭` and packaged with the Galois↔Frobenius bookkeeping
(`ConjClasses` of an abelian group are singletons, so `mk σ = mk τ ⇔ σ = τ`). The `_ne`
twin (line 213) is the complementary `σ ≠ τ` half giving `0`.

Variables / typeclasses (Lean side):
- `K L : Type*`, `[Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]` — the number-field Galois extension.
- `m : ℕ`, `[NeZero m]`, `[IsCyclotomicExtension {m} K L]` — forces `L = K(μ_m)`, hence `Gal(L/K)` abelian. **Used only** to obtain `IsMulCommutative Gal(L/K)` (the proof's first line).
- `[Fintype (galoisCharacter K L)]` — finiteness of the character group `Gal(L/K) →* ℂˣ`.
- `σ : Gal(L/K)`, `𝔭 : Ideal (𝓞 K)`, `[𝔭.IsPrime]`.

Hypotheses (Lean side):
- `_hunr : UnramifiedIn K L 𝔭` — unramifiedness. **Unused in the proof body** (underscore-named; verified: `hunr` does not appear in lines 199–208). Present for uniform call-shape with the `_ne` twin and the downstream `sum_charTwist_eq`.
- `_h : frobeniusClass K L 𝔭 = ConjClasses.mk σ` — the matching hypothesis; the only mathematical input.

Conclusion (math): `∑_{χ ∈ Ĝ} χ(σ)·χ(Frob 𝔭)⁻¹ = |G|`.

Conclusion (Lean): `(∑ χ : galoisCharacter K L, (χ σ : ℂ) * ((χ (frobeniusClass K L 𝔭).out : ℂ))⁻¹) = (Nat.card Gal(L/K) : ℂ)`.

**Proof body (verbatim, lines 199–208):**
```lean
  have : IsMulCommutative Gal(L/K) := IsCyclotomicExtension.isMulCommutative (S := {m}) K L
  set τ := (frobeniusClass K L 𝔭).out
  have hmk : ConjClasses.mk τ = frobeniusClass K L 𝔭 := Quotient.out_eq _
  have heq : σ * τ⁻¹ = 1 := by
    obtain ⟨c, hc⟩ : IsConj τ σ :=
      ConjClasses.mk_eq_mk_iff_isConj.mp (hmk.trans _h)
    rw [SemiconjBy, mul_comm' (c : Gal(L/K))] at hc
    rw [mul_right_cancel hc, mul_inv_cancel]
  rw [sum_galoisCharacter_mul_inv_eq K L σ τ, if_pos heq]
```
It is a **thin Galois-bookkeeping wrapper**: translate `frobeniusClass 𝔭 = mk σ` into
`σ·τ⁻¹ = 1` (using that conjugacy classes in an abelian group are singletons — `IsConj τ σ`
in a commutative group forces `τ = σ`), then discharge by the project-private
`sum_galoisCharacter_mul_inv_eq` (the if-then-else twisted orthogonality) with `if_pos`.
Mathematically identical to the `_ne` twin save for `heq : σ·τ⁻¹ = 1` / `if_pos` in place of
`hne : σ·τ⁻¹ ≠ 1` / `if_neg`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a corollary / one-case specialisation — not a `def`, not a named main result
(the file's sole `## Main results` entry is `chebotarev_cyclotomic`), and its proof is a
short `rw` over project-private helpers. (Lit width is exhaustive regardless.)

### One-line check (Phase 2b)

n/a — kind is `theorem`, not `def`/`abbrev`/`structure`. (Body is ~7 substantive lines.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                           | Hit? | Standard form found                              | Notes |
|----|----------------------------------|-------------------------------------------------------------------------------------------------|------|--------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "column orthogonality … sum over characters χ(g) equals order if g identity"                    | yes  | `∑_χ χ(g) = \|G\|·[g=1]` (column / second / dual orthogonality) | Conrad *Characters of Finite Abelian Groups*; UAlberta MAPH464 §2.8 *Orthogonality for characters*; Wikipedia *Character theory*; UCL *Characters of finite groups* notes |
|  2 | WebSearch (general / context)    | "Chebotarev density theorem cyclotomic case Frobenius character sum proof Sharifi Stevenhagen Lenstra" | yes  | the `∑_χ χ(σ)χ(𝔭)⁻¹ = \|G\| or 0` collapse        | Stevenhagen–Lenstra *Chebotarëv and his density theorem* (Leiden); Di Meglio notes; MIT 18.785 Lecture 28; Wikipedia — exact argument structure (cyclotomic case + L(1,χ)≠0) |
|  3 | WebSearch (named-after / aliases)| "second orthogonality relation group characters dual / column orthogonality nLab Pontryagin dual finite abelian" | yes  | same identity; *second / column / dual orthogonality relation* | nLab *Pontrjagin dual*; Conrad (short + long); name varies (column / dual / second), all standard; dual form `(1/\|G\|)∑_χ χ̄(g)χ(g')=δ(g,g')` |
|  4 | ChatGPT MCP                      | standard form + generality + historical evolution of character orthogonality                    | n/a  | (MCP down in this environment — task brief notes fallbacks) | substituted by Conrad + UAlberta + Stevenhagen–Lenstra primary sources, which fix the standard form and its generality unambiguously |
|  5 | Local references                 | grep `.mathlib-quality/references/` + `refs/Chebotarev/` for "orthogonality"                     | n/a  | references dir absent                            | `projects/Chebotarev/.mathlib-quality/references/` does not exist, and `refs/` is absent in this checkout (PDFs are local-only, ungitignored, not present). `PROJECT_OVERVIEW.md` cites Sharifi §7.2.1 (`docs/algnum.pdf` p.142) + Stevenhagen–Lenstra (`docs/cheb.pdf` p.18) as the source for this exact step |
|  6 | nLab                             | "character" / "Pontryagin duality" orthogonality                                                | yes  | orthogonality = unitarity of the Fourier/Pontryagin transform; double-dual `G ≅ Ĝ̂` | nLab frames it as Pontryagin self-duality of finite abelian groups (`Ĝ = Hom(G, U(1))`); abstract but same content |
|  7 | nCatLab                          | (categorical?) Pontryagin dual as `Hom(G, U(1))`                                                 | n/a  | not a categorical novelty                        | the statement is a finite-sum identity, not a categorical construction |
|  8 | Stacks Project                   | —                                                                                               | n/a  | not an algebraic-geometry concept                | character sums / Frobenius density are not Stacks-scope |
|  9 | MathOverflow / Math.SE           | "orthogonality relation dual group sum over characters" generality                              | yes  | confirmed for any finite abelian `G`, any field with enough roots of unity | standard; matches the mathlib `HasEnoughRootsOfUnity` hypothesis used by the project's generic engine |
| 10 | recent arXiv (last 5 yr)         | (scan within #1/#2 results)                                                                      | n/a  | nothing newer — 19th–20th-century classical character theory | no modern reformulation; the relation is stable |

The protocol passed: WebSearch ran 3 distinct queries at different levels (specific
identity, Chebotarev-context, aliases/nLab); ChatGPT MCP recorded `n/a` with reason (down)
and substituted with primary sources; local refs checked (`n/a`, absent); nLab checked
(hit); nCatLab / Stacks / arXiv each checked with `n/a` reason; MathOverflow/SE checked
(hit).

### Literature summary (Phase 3)

Concept identified as: **column (dual / "second") orthogonality relation for characters of
a finite abelian group**, here in its *twisted-difference* packaging
`∑_χ χ(σ)χ(τ)⁻¹ = |G|·[σ=τ]`, restricted to the **matching branch** `σ=τ` (value `|G|`),
and applied in the **cyclotomic Chebotarev** argument.
Sources agree on the standard form: **yes**.
Most general standard form: for any finite abelian group `G` and any field (or commutative
ring) `M` *with enough roots of unity* (`HasEnoughRootsOfUnity M (exp G)`),
`∑_{χ : G →* Mˣ} χ(g) = |G|·[g = 1]`; equivalently `∑_χ χ(σ)χ(τ)⁻¹ = |G|·[σ=τ]`.
Generality dimensions where the literature varies:
  - **codomain**: classically `ℂ`; the modern statement is any `M` with enough roots of unity (the project's own engine already uses this — see `CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity`).
  - **packaging**: bare `∑_χ χ(g)` (column) vs. twisted `∑_χ χ(σ)χ(τ)⁻¹` — related by `χ(τ)⁻¹ = χ(τ⁻¹)` and a reindex; both standard.
  - **branch**: the dichotomy `= |G| or 0`; this decl is the `= |G|` (diagonal/matching) half.
Disagreement with the literature: **none** — but the literature speaks about *the abelian
group* `G` directly. The target decl wraps `G = Gal(L/K)` in number-field/Frobenius
hypotheses (`NumberField`, `IsCyclotomicExtension`, `UnramifiedIn`, `frobeniusClass`,
`ConjClasses`) that play **no role** in the orthogonality content — they exist only to feed
the surrounding Chebotarev density proof.

---

### Generality analysis — `Chebotarev.character_orthogonality_cyclotomic_eq`

Literature-standard form (from Phase 3): `∑_{χ : G →* Mˣ} χ(σ)·χ(τ)⁻¹ = |G|·[σ=τ]` for a
finite abelian `G` and `M` with enough roots of unity (matching branch: `= |G|`).

| # | Parameter / hypothesis                                  | Current Lean form                  | Literature-standard form              | Weaker form exists? | Reason it can/can't be weakened |
|---|---------------------------------------------------------|------------------------------------|----------------------------------------|---------------------|----------------------------------|
| 1 | `[Field K] [NumberField K] [Field L] [NumberField L]`   | number fields                      | (absent — no field needed)             | yes (drop entirely) | orthogonality needs no number field; pure scaffolding for `frobeniusClass` |
| 2 | `[Algebra K L] [IsGalois K L]` + `m`, `[IsCyclotomicExtension {m} K L]` | cyclotomic Galois ext       | `G` abelian                            | yes (→ `[CommGroup G]` / `[IsMulCommutative G]`) | the *entire* role of `m`/cyclotomic is to give `IsMulCommutative Gal(L/K)` (proof line 1); replace by an abstract abelian `G` |
| 3 | `σ : Gal(L/K)`, `τ := (frobeniusClass K L 𝔭).out`       | Galois elt + Frobenius rep         | two elements `σ τ : G`                  | yes                 | `τ` is just an arbitrary element wearing a Frobenius hat |
| 4 | `𝔭 : Ideal (𝓞 K)`, `[𝔭.IsPrime]`, `_hunr : UnramifiedIn` | a prime ideal + unramifiedness    | (absent)                               | yes (drop entirely) | `_hunr` is **literally unused** (verified); `𝔭` only appears via `frobeniusClass 𝔭` = some element |
| 5 | codomain `ℂ`                                            | complex characters                 | `M` with `HasEnoughRootsOfUnity`       | yes                 | the underlying `sum_galoisCharacter_eq_card_or_zero` already routes through `HasEnoughRootsOfUnity`; `ℂ` chosen because it is alg. closed |
| 6 | `_h : frobeniusClass 𝔭 = ConjClasses.mk σ`             | Frobenius-class equality           | `σ·τ⁻¹ = 1` (i.e. `σ = τ`)             | yes                 | in an abelian group `mk` is injective on singleton classes; the `ConjClasses` wrapper is pure bookkeeping |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (drastically — by ~6 independent
scaffolding dimensions).
Number of weakening opportunities found: K = 6.

But the crucial observation is *not* "generalise this lemma". Stripping rows 1–6 to the
literature-standard form does **not yield a new lemma worth keeping** — it yields *exactly*
the already-existing project lemma `Chebotarev.sum_galoisCharacter_mul_inv_eq` (the twisted
column orthogonality `∑_χ χ(σ)·χ(τ)⁻¹ = if σ·τ⁻¹=1 then card else 0`, stated for abstract
`[IsMulCommutative Gal(L/K)]`), itself built on `sum_galoisCharacter_eq_card_or_zero`
(abstract `[Group G] [IsMulCommutative G] [Finite G]`), composed with one `if_pos`. The
general form is *already in the project, one layer down*, and the target decl is its
Galois-flavoured re-wrapping. So the relevant verdict axis is **composition / redundancy**,
not generality.

Proposed restatement: n/a for a *YES-generalise* — the maximally-general statement is the
existing `sum_galoisCharacter_mul_inv_eq` / `sum_galoisCharacter_eq_card_or_zero` (or,
upstream, the `MonoidHom`/`AddChar` column-orthogonality the project already plans to
contribute from `ForMathlib/CharacterOrthogonality.lean`). See Phase 6 / Phase 7.

Cost of "restatement": n/a (it would be a deletion + inline, not a re-proof).

### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Proposed reformulation | Mathlib downstream |
|----|--------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                      | partial  | drop number-field bundle; use `[CommGroup G]` (already a class) | — (abelian-ness is the only real hypothesis, already a class one layer down) |
|  2 | sequences/metric → filters/nets/topological?                            | no       | finite sum identity; no topology | — |
|  3 | construct object → universal-property class?                            | no       | it's an equation, not a construction | — |
|  4 | set-with-closure-predicate → bundled substructure?                      | no       | — | — |
|  5 | vector-space/field-specific → weaken typeclass hierarchy?               | yes      | codomain `ℂ` → `M` with `HasEnoughRootsOfUnity` | already realised in `sum_galoisCharacter_eq_card_or_zero`'s engine + mathlib `DirichletCharacter.sum_char_inv_mul_char_eq` |
|  6 | 1-categorical → higher/∞-categorical?                                   | no       | — | — |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive/monoid structure?          | no (this dimension is the **group** `G`, already arbitrary abelian once unwrapped) | — | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for *this decl as a mathlib candidate*).
One-line reason: the only "modernisations" (abstract abelian `G`, `HasEnoughRootsOfUnity`
codomain) are not improvements *to this lemma* — they collapse it into the already-existing
generic project lemma `sum_galoisCharacter_mul_inv_eq` (and, upstream, the general
`MonoidHom` column orthogonality mathlib already has *the building blocks* for, plus its
`DirichletCharacter` specialisation). The Galois/Frobenius wrapper has no mathlib-idiomatic
form because its content *is the wrapper*, and the wrapper is project-specific glue.

---

### Diamond / defeq risk — `Chebotarev.character_orthogonality_cyclotomic_eq`

n/a — declaration kind is `theorem` (introduces no definitional equality or
typeclass-search path). Phase 4.5 skipped.

---

### Mathlib search-status: `Chebotarev.character_orthogonality_cyclotomic_eq`

[A] Lean-Finder       (MCP unavailable here)                                    n/a: lean MCP not resolvable in this env (stale build); substituted by direct mathlib `grep` [D]
[B] Loogle            (MCP unavailable here)                                    n/a: same; the type mentions project-local `galoisCharacter`/`frobeniusClass`, which a mathlib index cannot contain anyway
[C] LeanSearch        (MCP unavailable here)                                    n/a: same
[D] Grep mathlib src  `frobeniusClass`, `Chebotarev`, `sum_eq_ite`, `sum_characters_eq`,
                      `sum_char_inv_mul_char_eq`, `card_monoidHom_of_hasEnoughRootsOfUnity`,
                      `exists_apply_ne_one_of_hasEnoughRootsOfUnity`, `orthogonal*` in
                      `GroupTheory/FiniteAbelian/`, `NumberTheory/DirichletCharacter/`,
                      `Algebra/Group/AddChar.lean`                                see below
[E] Name pattern      `character_orthogonality`, `sum_galoisCharacter`, `frobeniusClass` over `.lake/packages/mathlib/`   no hits

Grep findings (the load-bearing channel — run live against `.lake/packages/mathlib`):

- **`frobeniusClass` / `Chebotarev`: ZERO hits anywhere in mathlib.** The decl's exact form
  (a Galois Frobenius-class character sum) **cannot** exist in mathlib — it is built from
  project-local `frobeniusClass` (`Frobenius.lean:188`), `galoisCharacter`
  (`ZetaProduct.lean:71`), `UnramifiedIn`. Confirmed not-in-mathlib for the user's form.

- **Mathlib HAS a closely-related orthogonality lemma, but specialised to `DirichletCharacter`,
  not abstract `G`:**
  - `DirichletCharacter.sum_characters_eq` (`NumberTheory/DirichletCharacter/Orthogonality.lean:69`)
    — `∑ χ : DirichletCharacter R n, χ a = if a = 1 then (n.totient : R) else 0`. **Same statement
    and same proof skeleton** as the project's `sum_galoisCharacter_eq_card_or_zero`, but for
    `DirichletCharacter R n` (≅ `(ZMod n)ˣ →* …`), not an abstract finite abelian `G →* ℂˣ`.
  - `DirichletCharacter.sum_char_inv_mul_char_eq` (`Orthogonality.lean:81`)
    — `∑ χ : DirichletCharacter R n, χ a⁻¹ * χ b = if a = b then (n.totient : R) else 0`. This is
    **exactly the twisted-difference form** the target decl uses (`χ(σ)·χ(τ)⁻¹ = if σ=τ then …`),
    again specialised to `(ZMod n)`-indexed characters.
  → These are the *Dirichlet-character* incarnation of the same orthogonality. They are **not**
    applicable to `galoisCharacter K L = Gal(L/K) →* ℂˣ` (a different, abstract character group),
    and they do not mention `frobeniusClass`. So they are *not* a `NO-mathlib-has-it` hit for this
    decl; they confirm the **content is standard and mathlib-known**, reinforcing that the wrapper
    adds nothing mathlib-worthy.

- **The general (abstract-`G`) column-orthogonality sum is NOT packaged in mathlib** — only its
  building blocks are:
  - `AddChar.sum_eq_ite` (`Algebra/Group/AddChar.lean:329`) — the **dual / row** relation
    `∑_{a} ψ a = if ψ = 0 then card else 0` (sum over *group elements*, fixed character). This is
    the *transpose* of what we need (column = sum over characters), so not a match.
  - `CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity` (`GroupTheory/FiniteAbelian/Duality.lean:96`)
    — `|G →* Mˣ| = |G|`. **Directly used** by the project's `g=1` branch (`Cyclotomic.lean:176`).
  - `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity` (`Duality.lean:64`) — characters
    `G →* Mˣ` separate points. **Directly used** by the project's vanishing branch
    (`ForMathlib/CharacterOrthogonality.lean:48`).
  - `CommGroup.monoidHomMonoidHomEquiv` (`Duality.lean:147`) + `AddChar.doubleDualEmb`
    (`AddChar.lean:314`) — the double-dual machinery.
  → So the abstract column relation itself is a `derive`/contribute candidate **for the project's
    own `ForMathlib/CharacterOrthogonality.lean`** (or a future mathlib `feat`), not for this
    Galois decl.

Searched for both:
  - the user's current form (Galois Frobenius character sum) → **not in mathlib** (no `frobeniusClass`).
  - the literature-standard form (abstract twisted column orthogonality `∑_χ χ(σ)χ(τ)⁻¹ = card or 0`)
    → **not in mathlib as a standalone abstract-`G` lemma**; mathlib has the `DirichletCharacter`
    specialisation (`sum_char_inv_mul_char_eq`) and the double-dual building blocks, but not the
    `G →* Mˣ`-general sum.

Concluded: **not in mathlib** (all methods exhausted, both forms). The user's form is *two*
composition layers above the nearest mathlib primitives:
(mathlib `CommGroup.{exists_apply_ne_one, card_monoidHom}` / double-dual) → (generic abstract
column orthogonality, which lives in the project's `sum_galoisCharacter_eq_card_or_zero` /
`sum_galoisCharacter_mul_inv_eq` / `ForMathlib/CharacterOrthogonality.lean`) → (this
Galois-Frobenius `if_pos` wrapper).

---

### Call sites — `Chebotarev.character_orthogonality_cyclotomic_eq`

Internal use count: **K = 1** (excluding the declaring line 192).
External-to-file callers: 0 distinct files (the one caller is in the same file).

| Caller file:line                                            | Usage pattern (one-line excerpt)                                                |
|-------------------------------------------------------------|----------------------------------------------------------------------------------|
| `CebotarevDensity/Cyclotomic.lean:664`                      | `rw [← character_orthogonality_cyclotomic_eq K L m σ 𝔭 hunr h, …]` — inside the **private** `sum_charTwist_eq` |

Inline-derivation grep (was the equivalent re-derived elsewhere without using it?):
  - (none) — but the *twin* `character_orthogonality_cyclotomic_ne` (line 213) is the
    non-matching-case sibling with identical shape, used identically by `sum_charTwist_ne`
    (line 680). The two form a thin matched pair of adapters between the generic orthogonality
    `sum_galoisCharacter_mul_inv_eq` and the density proof.

Call-site signal: **K = 1 internal use only**, by a *private* lemma in the same file →
"possibly the wrong abstraction / could be inlined" (per the Phase 6.0.1 table this leans
toward NO-composable). It is a single-use private-facing adapter, not load-bearing API.

---

### Composition check (Phase 6)

Can `character_orthogonality_cyclotomic_eq` be derived from mathlib in ≤3 chained calls?

Strictly from *mathlib alone*: **no** — mathlib has neither `frobeniusClass` nor the
standalone abstract-`G` column-orthogonality lemma, so the literal statement is not 3 mathlib
calls. (Mathlib's `DirichletCharacter.sum_char_inv_mul_char_eq` is the same identity but on a
different, `ZMod`-indexed character group, and cannot be applied here.)

But the correct composition question for a *consolidation* verdict is: *is it a ≤3-call
composition of already-available decls (mathlib + the project's own generic engine)?*
**Yes, decisively** — its own proof is the witness:

Attempt 1 (the actual proof, ≤3 substantive steps after the `IsMulCommutative` instance):
```lean
  -- σ·τ⁻¹ = 1  ⟸  frobeniusClass 𝔭 = mk σ   (abelian ConjClasses singleton: IsConj τ σ ⟹ τ = σ)
  have heq : σ * τ⁻¹ = 1 := by
    obtain ⟨c, hc⟩ : IsConj τ σ := ConjClasses.mk_eq_mk_iff_isConj.mp (hmk.trans _h)
    rw [SemiconjBy, mul_comm' (c : Gal(L/K))] at hc
    rw [mul_right_cancel hc, mul_inv_cancel]
  rw [sum_galoisCharacter_mul_inv_eq K L σ τ, if_pos heq]
```
  - Decls used: `Chebotarev.sum_galoisCharacter_mul_inv_eq` (project, private) → which is itself
    `Finset.sum_congr` over `Chebotarev.sum_galoisCharacter_eq_card_or_zero` (project), which is
    `CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity` (mathlib, `g=1` branch) +
    `sum_char_apply_eq_zero_of_ne_one` (project `ForMathlib`, itself
    `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity` mathlib); plus `Quotient.out_eq`,
    `ConjClasses.mk_eq_mk_iff_isConj`, `mul_comm'`, `mul_right_cancel`, `mul_inv_cancel` (all mathlib).
  - Result: **succeeds** — a 1-`rw` finish on top of the generic twisted orthogonality plus a
    ~3-line `ConjClasses`-to-`σ·τ⁻¹=1` translation. No new mathematical idea.

Conclusion: **COMPOSABLE** — a thin (≤3-line) composition of `sum_galoisCharacter_mul_inv_eq`
(equivalently the generic column orthogonality) with `if_pos` and an abelian-`ConjClasses`
unfolding. The composition is mechanical glue, not a proof in disguise.

---

## Verdict: `Chebotarev.character_orthogonality_cyclotomic_eq`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature search (Phase 3): the content is the classical **column orthogonality** (matching
  branch) `∑_χ χ(σ)χ(τ)⁻¹ = |G|` for `σ=τ` (Conrad, UAlberta MAPH464, Wikipedia, nLab;
  Stevenhagen–Lenstra for the Chebotarev application). The decl wraps it in
  number-field/Frobenius scaffolding that carries no orthogonality content.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** by ~6 scaffolding
  dimensions; stripping them recovers the *already-existing* generic project lemma
  `sum_galoisCharacter_mul_inv_eq`, not a new contribution. No modern-idiom improvement.
- Mathlib search (Phase 5): **not in mathlib** in either form. Mathlib has the *same identity*
  for `DirichletCharacter` (`sum_char_inv_mul_char_eq`, `Orthogonality.lean:81`) and all the
  abstract building blocks (`CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity`,
  `card_monoidHom_of_hasEnoughRootsOfUnity`, the double-dual) — both used by the project — but
  not the abstract-`G` sum, and certainly not this Frobenius-flavoured wrapper.
- Composition check (Phase 6): **COMPOSABLE** — its own ≤3-line proof is the witness.
- Call sites (Phase 6.0): **K = 1**, a single private same-file consumer (`sum_charTwist_eq`,
  line 664).

**Rationale:**

This is a project-specific *Galois-bookkeeping wrapper*, not a mathlib candidate. The
mathematical content — the matching branch of column orthogonality for the characters of a
finite abelian group — is classical and belongs to character theory of `G` itself; mathlib
would never house it behind `NumberField`/`IsCyclotomicExtension`/`UnramifiedIn`/`frobeniusClass`
hypotheses, all of which are inert here (`_hunr` is verified-unused; the cyclotomic instance
only supplies abelian-ness via `IsCyclotomicExtension.isMulCommutative`; `ConjClasses.mk` is a
singleton-unfolding `IsConj τ σ ⟹ τ = σ`). The decl exists solely to translate "Frobenius class
of 𝔭 = class of σ" into "σ·τ⁻¹ = 1" and then read off the `then`-branch of the orthogonality
dichotomy via `if_pos`. It is the exact `if_pos` mirror of its `_ne` twin (verdict:
NO-composable, identical reasoning).

Crucially, the *generic* statement it specialises is **already present one layer down** as
`Chebotarev.sum_galoisCharacter_mul_inv_eq` / `sum_galoisCharacter_eq_card_or_zero` (and,
upstream, the project's own `ForMathlib/CharacterOrthogonality.lean`, which `PROJECT_OVERVIEW`
already routes toward a mathlib contribution). Mathlib independently confirms the identity is
standard by carrying it for `DirichletCharacter` (`sum_char_inv_mul_char_eq`). So there is no
mathlib gap *this decl* fills: the only gap that exists (a standalone abstract-`G` column
orthogonality `∑_{χ : G →* Mˣ} χ(g) = card·[g=1]` over `HasEnoughRootsOfUnity`, generalising the
`DirichletCharacter` version) is the job of the generic `CharacterOrthogonality` file, not of
this Frobenius-flavoured corollary. The decl is a 1-use private adapter; it should stay in the
project as glue and be inlined/kept local, not upstreamed.

(Note: this is *not* a `YES-but-generalise-first`. The "generalisation" of this lemma is not a
new mathlib lemma — it is literally the deletion of the wrapper down onto an existing project
lemma. And it is *not* `NO-mathlib-has-it`, because mathlib does **not** have the abstract-`G`
column-orthogonality sum applicable to `galoisCharacter`; it has only the `DirichletCharacter`
specialisation on a different character group and the double-dual building blocks. The
`DirichletCharacter` lemma cannot discharge this statement.)

**WHY not (refactor-actionable):**
Mathlib has the *building blocks* for the generic core (not for this Galois wrapper), both of
which the project already uses directly:
- `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity` — `Mathlib/GroupTheory/FiniteAbelian/Duality.lean:64` (the `g≠1` vanishing branch; used at `ForMathlib/CharacterOrthogonality.lean:48`)
- `CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity` — `Mathlib/GroupTheory/FiniteAbelian/Duality.lean:96` (the `g=1` branch; used at `Cyclotomic.lean:176`)
- `CommGroup.monoidHomMonoidHomEquiv` — `Mathlib/GroupTheory/FiniteAbelian/Duality.lean:147` (double dual)
- (the same identity, already packaged for the `ZMod`-indexed case:
  `DirichletCharacter.sum_char_inv_mul_char_eq` — `Mathlib/NumberTheory/DirichletCharacter/Orthogonality.lean:81`)

The project wraps these into `sum_galoisCharacter_eq_card_or_zero` →
`sum_galoisCharacter_mul_inv_eq`. The target decl itself is then a ≤3-line composition of *that*
lemma with `if_pos`.

Composition sketch (the decl from the generic project lemma, ≤3 lines — its own proof):
```lean
example : (∑ χ : galoisCharacter K L, (χ σ : ℂ) * ((χ (frobeniusClass K L 𝔭).out : ℂ))⁻¹)
    = (Nat.card Gal(L/K) : ℂ) := by
  have : IsMulCommutative Gal(L/K) := IsCyclotomicExtension.isMulCommutative (S := {m}) K L
  rw [sum_galoisCharacter_mul_inv_eq K L σ (frobeniusClass K L 𝔭).out,
      if_pos (by  -- σ·τ⁻¹ = 1 from frobeniusClass 𝔭 = mk σ, abelian ConjClasses singleton
        obtain ⟨c, hc⟩ : IsConj (frobeniusClass K L 𝔭).out σ :=
          ConjClasses.mk_eq_mk_iff_isConj.mp ((Quotient.out_eq _).trans h)
        rw [SemiconjBy, mul_comm' (c : Gal(L/K))] at hc
        rw [mul_right_cancel hc, mul_inv_cancel])]
```

Call sites in the project (from Phase 6.0): **K = 1** — `sum_charTwist_eq`
(`Cyclotomic.lean:664`, private).
Refactor plan:
1. **Keep this decl local to the project** (do *not* upstream it). It is correct, sorry-free
   glue serving the Chebotarev proof.
2. If a cleanup pass wants to shrink the surface: at the single call site `Cyclotomic.lean:664`,
   the `rw [← character_orthogonality_cyclotomic_eq …]` could inline the ≤3-line composition
   above directly into `sum_charTwist_eq` (and symmetrically inline the `_ne` twin into
   `sum_charTwist_ne` at line 680), then delete both `character_orthogonality_cyclotomic_{eq,ne}`.
   This is optional (1 use each) — the `PROJECT_OVERVIEW` Step-9 dedup table classifies the
   `_charTwist`/`_orthogonality` pair as **"keep-both (thin adapters)"**, so leaving them is
   acceptable.
3. The *real* upstreaming opportunity in this neighbourhood is **not** this decl but the generic
   `ForMathlib/CharacterOrthogonality.lean` lemmas (`sum_char_apply_eq_zero_of_ne_one` et al.) →
   mathlib, generalising the existing `DirichletCharacter` orthogonality from `(ZMod n)ˣ` to an
   arbitrary finite abelian `G` (an abstract-`G` `∑_{χ : G →* Mˣ} χ(g) = card·[g=1]`). Tracked
   separately in the overview.

Next action: **delete-or-keep-local** — this decl is *not* a mathlib contribution. No PR.
Optionally inline at its single call site (`Cyclotomic.lean:664`) during a `/cleanup` pass,
together with its `_ne` twin; otherwise keep both as the documented thin adapters. Direct any
mathlib energy to the generic `CharacterOrthogonality` → mathlib (abstract-`G` orthogonality)
route instead.

---

## Next step

NO-composable-from-mathlib: this is project-local Galois glue (a ≤3-line `if_pos` wrapper over
the project's own generic orthogonality `sum_galoisCharacter_mul_inv_eq`). Do **not** upstream
it. Optionally inline at its single private call site (`Cyclotomic.lean:664`) during cleanup,
together with its `_ne` twin; otherwise keep both as the overview's sanctioned "thin adapters".
Mathlib-contribution effort in this area belongs to generalising the existing
`DirichletCharacter` orthogonality to an abstract finite abelian `G` (from the project's
`ForMathlib/CharacterOrthogonality.lean`), not to this Frobenius-flavoured corollary.
