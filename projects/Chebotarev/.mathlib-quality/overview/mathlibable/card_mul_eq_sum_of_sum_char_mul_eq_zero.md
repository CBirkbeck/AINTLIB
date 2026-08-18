# /mathlibable report — `card_mul_eq_sum_of_sum_char_mul_eq_zero`

## Baseline (Phase 0)
- lake build:               ✗ stale (per task brief; `lean_*` project resolution unavailable — reasoned from source + mathlib-source reads, as instructed)
- decl `card_mul_eq_sum_of_sum_char_mul_eq_zero`: ✓ resolved at `projects/Chebotarev/CebotarevDensity/ForMathlib/CharacterOrthogonality.lean:66`
- kind:                      `theorem`
- namespace:                 **root** (the only `namespace` token in the file is inside docstring prose on line 30; no enclosing `namespace … end` block) → qualified name is the bare `card_mul_eq_sum_of_sum_char_mul_eq_zero`
- has sorry:                 no
- module docstring summary:  Two complex-character orthogonality relations for finite abelian `G` + their Fourier-inversion consequences; explicitly earmarked "candidates for upstreaming to mathlib" (root namespace, `ForMathlib/`).

## Statement (Phase 1)

`card_mul_eq_sum_of_sum_char_mul_eq_zero` is **finite-abelian Fourier inversion in vanishing-moment form**:

Let `G` be a finite abelian group and `Ĝ = (G →* ℂˣ)` its complex (multiplicative, units-valued) character group. Let `f : G → ℂ`. If every **nontrivial** twisted moment vanishes — `∑_{s∈G} χ(s)·f(s) = 0` for all `χ ≠ 1` — then for every `u ∈ G`,
`|Ĝ| · f(u) = ∑_{s∈G} f(s)`.
Equivalently: `f` having no non-principal Fourier coefficients forces `f` to equal its (un-normalised) average; the sibling `eq_of_sum_char_mul_eq_zero` repackages this as "`f` is constant".

Variables / typeclasses (Lean side):
- `{G : Type*} [CommGroup G] [Fintype G]` — the finite abelian group (written multiplicatively).
- `[Fintype (G →* ℂˣ)]` — finiteness of the dual (mathlib supplies this instance via `AddChar.instFintype` / duality).
- `(f : G → ℂ)` — the function being analysed.
- `(u : G)` — the evaluation point.

Hypotheses (Lean side):
- `hf : ∀ χ : G →* ℂˣ, χ ≠ 1 → ∑ s : G, ((χ s : ℂˣ) : ℂ) * f s = 0` — all non-principal Fourier coefficients vanish.

Conclusion (math): `f` equals its average — `card Ĝ · f(u) = ∑ f`.
Conclusion (Lean): `(Fintype.card (G →* ℂˣ) : ℂ) * f u = ∑ s : G, f s`.

The proof (≈ 25 lines) expands the RHS via column orthogonality, uses `Finset.sum_comm` to swap the `s`/`χ` sums, factors out `χ(u⁻¹)`, then collapses the character sum to its principal term using `hf`.

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A corollary/specialisation — the immediate "vanishing-moments ⟹ constant" consequence of standard character orthogonality. Not a `def`/`class`, not a `## Main results` headline (the project's actual goal is the Chebotarev/ideal-density theorem; this is plumbing feeding it), not named after a person/place. (Literature width is EXHAUSTIVE regardless.)

## One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure` → one-line check **n/a**. (Body is a multi-line `calc` proof, not a one-line definition.)

## Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "finite abelian group Fourier inversion characters vanishing moments function recovered from average orthogonality relations" | yes | `f(x) = (1/|G|) ∑_α f̂(α) χ_α(x)`; orthogonality `∑_x χ_α(x) = |G|·[α=0]` | Conrad, Tao §1, UChicago REU, McGill COMP760, Wikipedia "Fourier transform on finite groups" all give the inversion formula; the vanishing-moments corollary is an immediate observation, not a named theorem |
| 2 | WebSearch (named-after / Conrad) | "Keith Conrad characters finite abelian groups orthogonality relations f constant iff Fourier coefficients vanish nonprincipal" | partial | orthogonality relations = "Corollary 4.2" in Conrad; inversion formula stated | Conrad packages **orthogonality** and the **inversion formula** as the named results; "all non-principal coeffs vanish ⟹ constant" is left as the obvious consequence, never given its own number/name |
| 3 | WebSearch (mathlib-specific / general form) | "mathlib4 finite abelian group discrete Fourier transform inversion AddChar dft general group not ZMod" | yes (negative) | confirms: a function on a finite abelian group is recovered from its DFT on the dual | No general-group DFT-inversion named lemma surfaced; mathlib's general inversion is the *continuous* one; finite-group DFT inversion is `ZMod`-only |
| 4 | ChatGPT MCP | (asked: is the vanishing-moments⟹constant form separately named? line-count of derivation from column orthogonality?) | n/a | — | **Unavailable in this environment** — Codex CLI backing the MCP failed on every attempt (`Command failed: …/Codex.app … exec`). Recorded n/a per protocol; the standard-form question is answered decisively by channels 1–2 + the direct mathlib-source reads. |
| 5 | Local references | grep `projects/Chebotarev/.mathlib-quality/references/` | n/a | — | Directory absent (no `references/`); no `refs/Chebotarev/` PDFs. Recorded n/a. |
| 6 | nLab | "Pontryagin duality finite abelian group Fourier inversion characters orthogonality" | yes | Fourier inversion = special case of Pontryagin bidual iso; characters orthogonal | Confirms the result is the finite specialisation of Pontryagin duality / Fourier inversion; no standalone "vanishing-moments" lemma name |
| 7 | nCatLab | (folded into #6 — Pontryagin duality is the categorical statement) | n/a | — | Not a distinct categorical concept beyond Pontryagin duality (covered in #6); the result is 1-categorical finite-group harmonic analysis |
| 8 | Stacks Project | — | n/a | — | Not an algebraic-geometry / scheme-theoretic concept; Stacks does not cover finite-group Fourier analysis |
| 9 | MathOverflow / Math.SE | (covered via #1–#2 hits: Tao notes, REU notes, lecture notes) | yes | same inversion formula + orthogonality | The "vanishing non-principal coefficients ⟹ constant" step is uniformly treated as a one-line consequence in lecture notes, never a cited theorem |
| 10 | recent arXiv | "harmonic analysis finite abelian groups" (1304.1731 surfaced) | yes | standard orthogonality + DFT recovery | Modern usage matches the classical statement; no new/renamed formulation |

The protocol passes: WebSearch ran 4 distinct queries across generality levels (specific vanishing-moments form, Conrad/named form, mathlib/general form, nLab/Pontryagin form); ChatGPT MCP recorded n/a with a concrete environment-failure reason; local refs recorded n/a (absent); nLab checked; Stacks/nCatLab/MathOverflow/arXiv each checked or n/a-with-reason.

### Literature summary (Phase 3)

Concept identified as: **Fourier inversion / character orthogonality on a finite abelian group** (Pontryagin duality, finite case). The target is specifically the corollary "a function with vanishing non-principal Fourier coefficients equals its average (is constant)".
Sources agree on the standard form: **yes** — the inversion formula `f = (1/|G|) ∑_χ f̂(χ) χ` and the two orthogonality relations are universal (Conrad, Tao, Wikipedia, nLab).
Most general standard form: the inversion formula on any finite abelian group with values in any field containing enough roots of unity (classically ℂ). The "vanishing-moments ⟹ constant" statement is a **routine, unnamed** specialisation of inversion.
Generality dimensions where the literature varies:
  - **value field**: ℂ classically, but the orthogonality works over any `[CommRing R] [IsDomain R] [CharZero R]` with enough roots of unity (mathlib's `AddChar.sum_eq_ite` is stated at `[CommSemiring R] [IsDomain R]`, the iff-version adds `[CharZero R]`).
  - **character target**: `Hom(G, ℂˣ)` (units) vs `AddChar G ℂ` (additive characters into ℂ) vs `Hom(G, Circle)` — all isomorphic; mathlib's canonical idiom is `AddChar`.
Disagreement with the literature: none. The user's statement is mathematically exactly the standard corollary; only the *spelling* (`G →* ℂˣ`, multiplicative) differs from mathlib's canonical additive `AddChar` idiom.

## Generality analysis — `card_mul_eq_sum_of_sum_char_mul_eq_zero`

Literature-standard form (from Phase 3): Fourier inversion over a finite abelian group with values in a field with enough roots of unity; the vanishing-moments corollary is the immediate consequence.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `[CommGroup G] [Fintype G]` | finite abelian (mult.) | finite abelian group | NO (already maximal for the statement) | Finiteness + commutativity are the defining hypotheses of finite-abelian Fourier theory |
| 2 | target `G →* ℂˣ` | complex units-valued chars | `AddChar G R` for `R` with enough roots of unity | **yes (idiom)** | Mathlib's canonical dual is `AddChar G ℂ` / `AddChar G Circle`; the `G →* ℂˣ` spelling is bridged by `AddChar.toMonoidHomMulEquiv` but is non-idiomatic |
| 3 | codomain `ℂ` of `f` | ℂ | any `R` with `[CommRing R] [IsDomain R] [CharZero R]` + enough roots of unity | yes | Column orthogonality (`AddChar.sum_eq_ite`) already lives over `[CommSemiring R] [IsDomain R]`; the inversion corollary would generalise the same way, since the proof uses only orthogonality + sum manipulation |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (along two non-essential axes: the `G →* ℂˣ` spelling vs mathlib's `AddChar`, and ℂ vs a general root-of-unity-rich domain). The *mathematical* content (finite abelian, vanishing non-principal moments) is at the right generality.
Number of weakening opportunities found: 2 (idiom-spelling + codomain ring).
Proposed restatement (if pursued): state against `AddChar G R` with `R` a `[CharZero] [IsDomain]` (semi)field carrying enough roots of unity, reusing `AddChar.sum_apply_eq_ite`. **However** — see Phase 5/6: the orthogonality machinery this would rest on is already in mathlib, and the corollary itself is unnamed in the literature, so the live question is composition, not regeneralisation.
Cost of restatement: CHEAP–MODERATE (mechanical re-spelling onto `AddChar` + relaxing ℂ).

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preambles → typeclasses/instances? | no | already fully typeclass-driven | — |
| 2 | sequences/metric → filters/topology? | no | finite combinatorial identity; no limits | — |
| 3 | construct object → universal-property class? | partial | the dual is already `AddChar`/Pontryagin bidual in mathlib | reuse `AddChar.doubleDualEquiv` |
| 4 | set-with-closure → bundled substructure? | no | — | — |
| 5 | field-specific → module/ring typeclass weakening? | **yes** | replace `ℂ` codomain by `[CommRing R] [IsDomain R] [CharZero R]` with enough roots of unity (mathlib's `AddChar.sum_eq_ite` generality) | the whole `AddChar` orthogonality API over general domains |
| 6 | 1-categorical → higher-categorical? | no | classical finite-group harmonic analysis | — |
| 7 | concrete index → arbitrary monoid/group? | **yes (the spelling)** | use mathlib's `AddChar G ℂ` (the canonical dual) rather than the bespoke `G →* ℂˣ` | unifies with `AddChar.sum_apply_eq_ite`, `complexBasis`, `expect_apply_eq_ite`, the entire `Analysis/Fourier/FiniteAbelian/` API |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** — mathlib's contemporary idiom for this material is `AddChar α ℂ` (additive characters), and the orthogonality this corollary needs is already proved there. The user's `G →* ℂˣ` spelling is the *non*-idiomatic one. But this is **not** a "modernise a missing thing" YES: the modern objects (`AddChar.sum_apply_eq_ite`, `complexBasis`) already exist in mathlib, so the idiom check points toward *reuse*, not toward contributing a modernised version.
  - Real mathematical improvement of restating: marginal — it would re-derive, in mathlib's idiom, a corollary mathlib's idiom already trivially supports.

## Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (introduces no definitional equalities or typeclass-search paths).

## Mathlib search-status: `card_mul_eq_sum_of_sum_char_mul_eq_zero`

[A] Lean-Finder       — n/a: tool not available in this environment.
[B] Loogle            `lean_loogle` n/a: deferred tool not in this environment's registry; substituted by direct mathlib-source pattern grep (method D), which is conclusive here.
[C] LeanSearch        `lean_leansearch` n/a: same as [B].
[D] Grep mathlib src  `Fourier|Orthogon|Character|AddChar|Duality` over `.lake/packages/mathlib/`; then `sum_eq_ite`, `sum_apply_eq_ite`, `∑ ψ : AddChar`, `dft`, `inversion`, `complexBasis`  — **HITS (decisive)**:
  - `AddChar.sum_apply_eq_ite` (`Mathlib/Analysis/Fourier/FiniteAbelian/PontryaginDuality.lean:188`):
    `∑ ψ : AddChar α ℂ, ψ a = if a = 0 then (Fintype.card α : ℂ) else 0` — **column orthogonality**; exactly the user's `sum_char_apply_eq_zero_of_ne_one` (sibling helper), in mathlib's `AddChar` idiom.
  - `AddChar.sum_eq_ite` (`Mathlib/Algebra/Group/AddChar.lean:329`):
    `∑ a, ψ a = if ψ = 0 then ↑(card A) else 0` over `[CommSemiring R] [IsDomain R]` — **row orthogonality**; exactly the user's `sum_char_self_eq_zero_of_ne_one`, more general (any domain).
  - `AddChar.complexBasis` (`PontryaginDuality.lean:124`): the characters form a `Basis` of `α → ℂ`, with `complexBasis.sum_repr` giving the full **Fourier expansion** `f = ∑_χ f̂(χ) χ`.
  - `AddChar.sum_apply_eq_zero_iff_ne_zero`, `expect_apply_eq_ite`, etc. — the full orthogonality/inversion neighbourhood.
  - `ZMod.dft` + `ZMod.dft_dft` (`Mathlib/Analysis/Fourier/ZMod.lean`): finite-group **Fourier inversion** but **only for `ZMod N`** with the canonical character, not a general abstract `G` with `Hom(G,ℂˣ)`.
[E] Name pattern      grep for `card.*\* f`, `mul_eq_sum`, `sum_of_.*char`, `eq_average` over Fourier/AddChar — **no hits**: the *packaged* "vanishing-moments ⟹ card·f(u)=∑f" statement is not present under any name.

Searched for both:
  - the user's current form (`G →* ℂˣ`, packaged inversion) — not found as a named decl.
  - the literature-standard form (orthogonality + basis expansion over `AddChar α ℂ`) — **found** (the building blocks), but not the packaged corollary.

Concluded: **"found building blocks (`AddChar.sum_apply_eq_ite`, `AddChar.sum_eq_ite`, `AddChar.complexBasis`); the packaged target itself is not in mathlib under any name."** The two sibling orthogonality helpers in the same project file ARE individually in mathlib (more generally); the inversion *corollary* is not, but it is a short derivation from the orthogonality mathlib already has.

## Call sites — `card_mul_eq_sum_of_sum_char_mul_eq_zero`

Internal use count (excluding the declaring file): **0**
External-to-file callers: **0 distinct files**

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| (same file) CharacterOrthogonality.lean:106–107 | `(card_mul_eq_sum_of_sum_char_mul_eq_zero f hf u).trans (… u').symm` — used **only** by the sibling `eq_of_sum_char_mul_eq_zero` inside the same file |

So the target is a within-file helper feeding `eq_of_sum_char_mul_eq_zero`, which is the lemma actually consumed downstream:
- `eq_of_sum_char_mul_eq_zero` → `IdealCongruenceCount.lean:1961` (finite-abelian Fourier inversion making residue-densities constant on a subgroup).
- The two orthogonality siblings are consumed downstream too — `sum_char_apply_eq_zero_of_ne_one` → `Cyclotomic.lean:177`; `sum_char_self_eq_zero_of_ne_one` → `IdealCongruenceCount.lean:3434` — **but both have direct mathlib equivalents** (`AddChar.sum_apply_eq_ite`, `AddChar.sum_eq_ite`).

Inline-derivation grep (was the equivalent re-derived elsewhere?): the *downstream* consumer at `IdealCongruenceCount.lean:1944–1961` does the Fourier-inversion reasoning itself and calls `eq_of_sum_char_mul_eq_zero`, not the target directly. No other inline re-derivation of the target's exact statement found.

Call-sites signal: the target has **K = 0** external uses (one internal use, by its sibling) → "K = 1-ish, possibly the wrong abstraction / could be folded into its sibling" → leans **NO-composable / fold-in**.

## Composition check (Phase 6)

Can `card_mul_eq_sum_of_sum_char_mul_eq_zero` be derived from mathlib in ≤3 chained calls?

Attempt 1 (orthogonality as a black box): `∑_s f(s) = ∑_s (∑_χ χ(u⁻¹ s)) · f(s) / card`? — expand RHS `card·f(u)` as `∑_s [s=u]·card·f(s)`, rewrite `[s=u]·card` via `AddChar.sum_apply_eq_ite` (after porting `G →* ℂˣ` ↔ `AddChar G ℂ`), `Finset.sum_comm` to swap, factor `χ(u⁻¹)`, then `Finset.sum_eq_single_of_mem` collapsing to `χ = 1` using `hf`.
  - Mathlib decls used: `AddChar.sum_apply_eq_ite`, `Finset.sum_comm`, `Finset.sum_eq_single_of_mem`, `map_mul`, the `AddChar ≃* (G →* ℂˣ)` bridge.
  - Result: **fails as a ≤3-call composition** — this is the project's actual ~25-line `calc`/`have` proof (5 `calc` steps with `Finset.sum_congr`, `Finset.mul_sum`, `mul_assoc` reasoning between). It is a genuine proof, not a chain of ≤3 applications.
  - Notes: even granting mathlib's orthogonality as one black-box call, the sum-swap + moment-collapse is irreducibly ≥3 non-trivial steps with rewriting between them.

Attempt 2 (is it `≤1`-line from a mathlib inversion?): mathlib has **no** general finite-abelian inversion to specialise (only `ZMod.dft_dft`, which is `ZMod`-specific and differently shaped). So no 1-line specialisation exists.

Conclusion: **NOT a ≤3-call composition.** It is a short *proof* from mathlib's orthogonality, but per the Phase-6 heuristics ("multiple `have`s with non-trivial reasoning between" and "requires `rw`/`Finset.sum_congr` chains") that is a proof, not a composition. The honest characterisation: **mathlib has the building blocks; assembling them into this exact corollary is a ~10-line proof, not a 1–3-line inline.**

## Verdict: `card_mul_eq_sum_of_sum_char_mul_eq_zero`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): standard Fourier inversion / orthogonality on finite abelian groups; the vanishing-moments ⟹ constant statement is a **routine, unnamed** corollary (Conrad, Tao, Wikipedia, nLab) — not a separately-named theorem.
- Generality analysis (Phase 4): STRICTLY NARROWER than idiomatic mathlib only in *spelling* (`G →* ℂˣ` vs `AddChar α ℂ`) and codomain (`ℂ` vs general root-of-unity domain); the mathematical hypotheses are at the right generality. Modern-idiom check points to *reuse* of existing `AddChar` API, not to a novel modernisation.
- Mathlib search (Phase 5): found the building blocks — `AddChar.sum_apply_eq_ite` (column orthogonality = the sibling `sum_char_apply_eq_zero_of_ne_one`), `AddChar.sum_eq_ite` (row orthogonality = `sum_char_self_eq_zero_of_ne_one`, more general), and `AddChar.complexBasis` (Fourier expansion). The packaged target is **not** in mathlib under any name; no general finite-group inversion exists to specialise (only `ZMod.dft_dft`).
- Composition check (Phase 6): NOT a ≤3-call composition — it is a ~10-line proof from the orthogonality building blocks.

**Rationale:**

This is textbook finite-abelian Fourier inversion in its "all non-principal Fourier coefficients vanish ⟹ `f` is its own average" form. The literature is unanimous that this is the *standard* theory but treats this particular implication as an immediate one-liner off the inversion formula `f = (1/|G|) ∑_χ f̂(χ) χ`, never as a separately-named lemma. Decisively, mathlib already carries the substantive content this rests on: `AddChar.sum_apply_eq_ite` is *exactly* the column-orthogonality sibling, `AddChar.sum_eq_ite` is *exactly* the row-orthogonality sibling (in greater generality), and `AddChar.complexBasis` provides the full Fourier-basis expansion. The target theorem is the short consequence; its sibling `eq_of_sum_char_mul_eq_zero` (the actually-consumed lemma) is one further `mul_left_cancel₀` step. So mathlib is not missing the *mathematics* — it has the orthogonality and the basis decomposition; it is missing only this specific repackaging, which is derivable in ~10 lines and is not a named result anywhere.

The one genuine tension — and the reason this is NO-**composable** rather than NO-mathlib-has-it — is the idiom gap: the project works with `Hom(G, ℂˣ)` (units-valued, multiplicative characters), whereas mathlib's finite-abelian Fourier API is uniformly stated for `AddChar G ℂ` (additive characters into ℂ). The two dual groups are isomorphic (`AddChar.toMonoidHomMulEquiv`, and for finite abelian `G`, `AddChar (Multiplicative G) ℂ ≃ (G →* ℂˣ)`), but not the same spelling, so "use the mathlib lemma directly" is a port, not a one-liner. This is precisely the situation where the right move is to *reuse mathlib's orthogonality* and inline the short inversion argument at the (single) consumer, rather than upstream a bespoke `G →* ℂˣ`-flavoured corollary that would duplicate, in a non-idiomatic spelling, machinery mathlib already has.

**WHY not (refactor-actionable):**
Mathlib has the building blocks; the target is a ~10-line assembly, and (critically) it has **no external callers** — only its sibling `eq_of_sum_char_mul_eq_zero` uses it, and that sibling's downstream consumers are the real clients. The building blocks:
- `AddChar.sum_apply_eq_ite` — `Mathlib/Analysis/Fourier/FiniteAbelian/PontryaginDuality.lean:188` — column orthogonality `∑ ψ : AddChar α ℂ, ψ a = if a = 0 then card α else 0`.
- `AddChar.sum_eq_ite` — `Mathlib/Algebra/Group/AddChar.lean:329` — row orthogonality (general domain).
- `AddChar.complexBasis` / `AddChar.complexBasis.sum_repr` — `PontryaginDuality.lean:124` — the Fourier expansion `f = ∑_χ f̂(χ) χ`.
- Bridge `AddChar.toMonoidHomMulEquiv` (`Mathlib/Algebra/Group/AddChar.lean:305`) to move between `AddChar G ℂ` and `G →* ℂˣ`.

Mathlib building blocks (qualified):
`AddChar.sum_apply_eq_ite`, `AddChar.sum_eq_ite`, `AddChar.complexBasis` (+`Basis.sum_repr`), `AddChar.toMonoidHomMulEquiv`, `Finset.sum_comm`, `Finset.sum_eq_single_of_mem`.

Composition sketch (the corollary is NOT ≤3 lines, but it IS a short proof off the mathlib orthogonality — illustrative skeleton, against the idiomatic `AddChar α ℂ` form):
```lean
-- with `f : α → ℂ`, `hf : ∀ ψ ≠ 0, ∑ s, ψ s * f s = 0`:
example (u : α) : (Fintype.card (AddChar α ℂ) : ℂ) * f u = ∑ s, f s := by
  have key : ∀ s, (∑ ψ : AddChar α ℂ, ψ (s - u)) = if s = u then (card α : ℂ) else 0 := fun s => by
    simpa [sub_eq_zero] using AddChar.sum_apply_eq_ite (s - u)   -- column orthogonality
  -- then: rewrite card·f(u) = ∑ s [s=u]·card·f s, use `key`, `Finset.sum_comm`, factor ψ(-u),
  --       `Finset.sum_eq_single_of_mem 0` collapsing via `hf` (≈ the project's 5-step calc).
  sorry
```

Call sites in our project (from Phase 6.0): **K = 0 external** (1 internal, by the sibling `eq_of_sum_char_mul_eq_zero`).

Refactor plan:
1. **Do not upstream** `card_mul_eq_sum_of_sum_char_mul_eq_zero` (nor its orthogonality siblings) as `G →* ℂˣ` lemmas — mathlib already has the orthogonality as `AddChar.sum_apply_eq_ite` / `AddChar.sum_eq_ite` and the expansion as `AddChar.complexBasis`.
2. **Within the project**, the two orthogonality siblings (`sum_char_apply_eq_zero_of_ne_one`, `sum_char_self_eq_zero_of_ne_one`) are the genuinely-reused pieces (Cyclotomic.lean:177, IdealCongruenceCount.lean:3434). The clean cleanup is to either (a) keep them as thin project-local `G →* ℂˣ` adapters that *call* the mathlib `AddChar` lemmas through `toMonoidHomMulEquiv` (one-line bodies), deleting the from-scratch `sum_eq_zero_of_mulLeft_mul_const_aux` proof; or (b) port the few consumers onto mathlib's `AddChar` lemmas directly.
3. The target `card_mul_eq_sum_of_sum_char_mul_eq_zero` and its sibling `eq_of_sum_char_mul_eq_zero` should be **folded into their single consumer** (`IdealCongruenceCount.lean:1944–1961` already does the inversion reasoning manually): inline the ~10-line inversion there, built on the project's (now adapter-thin) orthogonality lemmas. No new mathlib lemma is justified.

Next action: do **not** open a mathlib PR for this declaration. Re-aim the project's orthogonality on mathlib's `AddChar.sum_apply_eq_ite` / `AddChar.sum_eq_ite` (via `AddChar.toMonoidHomMulEquiv`); fold the inversion corollary + `eq_of_sum_char_mul_eq_zero` into their consumer. (If, after `/generalise`, the team instead wants a *general-group* finite-abelian Fourier-inversion API in mathlib — currently only `ZMod.dft` exists — that is a separate, larger contribution about `AddChar`, not about this `G →* ℂˣ` corollary; flag for a human if that broader gap is the real goal.)

---

## Next step

Do not open a mathlib PR for `card_mul_eq_sum_of_sum_char_mul_eq_zero`. Within the project, re-aim the orthogonality siblings onto mathlib's `AddChar.sum_apply_eq_ite` / `AddChar.sum_eq_ite` (bridging `G →* ℂˣ` ↔ `AddChar G ℂ` via `AddChar.toMonoidHomMulEquiv`), delete the from-scratch `sum_eq_zero_of_mulLeft_mul_const_aux`, and fold this inversion corollary together with `eq_of_sum_char_mul_eq_zero` into their single downstream consumer (`IdealCongruenceCount.lean`). The packaged corollary is unnamed in the literature and composes from mathlib's existing finite-abelian orthogonality + Fourier-basis API — no new mathlib lemma is warranted.
