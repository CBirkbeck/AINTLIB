# /mathlibable report — `Chebotarev.subgroup_eq_top_of_forall_frobenius_mem`

## Baseline (Phase 0)

- lake build:               not run (local build stale per task brief; reasoning from source + mathlib tree on pin `d90090f`, toolchain `v4.31.0-rc2`)
- decl `Chebotarev.subgroup_eq_top_of_forall_frobenius_mem`: ✓ resolved at `projects/Chebotarev/CebotarevDensity/CyclotomicNormResidue.lean:592`
- qualified name VERIFIED: `Chebotarev.subgroup_eq_top_of_forall_frobenius_mem` (namespace `Chebotarev` opened L36, `end Chebotarev` L601; the parsed guess was correct)
- kind:                      theorem
- has sorry:                 no (body is a one-line application of `subgroup_eq_top_of_forall_frobenius_mem_of_coprime … K L 1`)
- module docstring summary:  Two arithmetic inputs of Frobenius-fibre equidistribution: the cyclotomic Frobenius-as-norm-residue, and "Frobenii generate the Galois group" (CFT-free, via the project's zeta asymptotics).

## Statement (Phase 1)

`subgroup_eq_top_of_forall_frobenius_mem` states the following:

> Let `L/K` be a finite Galois extension of number fields with **abelian** Galois group
> `G = Gal(L/K)`. Let `H ≤ G` be a subgroup. If, for every nonzero prime `𝔭` of `K` that is
> unramified in `L`, the chosen representative `(frobeniusClass K L 𝔭).out` of the Frobenius
> conjugacy class lies in `H`, then `H = G` (`H = ⊤`).

This is the classical statement **"the Frobenius elements of the unramified primes generate the
Galois group"**, in its subgroup-membership packaging: the only subgroup containing every Frobenius
is the whole group. Equivalently, the fixed field of such an `H` has no nontrivial unramified-prime
behaviour and so collapses to `K`.

Variables / typeclasses (Lean side):
- `K L : Type*`, both number fields (`[Field _] [NumberField _]`), `[Algebra K L]`, `[IsGalois K L]` — finite Galois extension of number fields.
- `[IsMulCommutative Gal(L/K)]` — **`G` abelian** (added vs. the classical statement; see Generality).
- `H : Subgroup Gal(L/K)` — the candidate subgroup.

Hypotheses (Lean side):
- `hH : ∀ 𝔭, 𝔭.IsPrime → 𝔭 ≠ ⊥ → UnramifiedIn K L 𝔭 → ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) ∈ H` — `H` contains the chosen Frobenius **representative** `.out` of every unramified prime (NOT the whole conjugacy class).

Conclusion (math): `H = G`.
Conclusion (Lean): `H = ⊤`.

Proof (as written): two-line reduction. `Subgroup.card_eq_iff_eq_top` reduces `H = ⊤` to a cardinality
equation; `IsGalois.card_aut_eq_finrank` + `IntermediateField.finrank_fixedField_eq_card` +
`Module.finrank_mul_finrank` reduce that to `[fixedField H : K] = 1`; the substantive input
`finrank_fixedField_le_one_of_forall_frobenius_mem` (project lemma, via the coprime variant with
`m = 1`) supplies `[F:K] ≤ 1`. That bound is itself the **entire zeta-asymptotic Chebotarev argument**:
compare `Σ_𝔭 N𝔭^{-s} ~ log(1/(s-1))` for `K` and for `F = fixedField H` and use the `[F:K]`-fold
multiplicity of split primes to force `[F:K] ≤ 1`.

## Size classification (Phase 2a)

Verdict: **BIG**
Reason: It is a named *Main result* of the file (listed in the module docstring `## …` bullet, L22–29)
and is a theorem with a classical name ("Frobenii generate the Galois group" — a standard corollary of
Chebotarev density). Both BIG triggers fire. (Literature width is EXHAUSTIVE regardless.)

## One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure` — one-line check **n/a**. (The body is a one-line
forwarding to the coprime variant, but that is a proof term, not a one-line *definition*; the gate
does not apply.)

## Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "Frobenius elements unramified primes generate Galois group … abelian extension theorem"               | yes  | Frob of unramified primes generate `Gal(L/K)`; for abelian `G`, Artin symbol well-defined | wstein ANT, MIT 18.785 LectureNotes7, Kedlaya artin.pdf — all state it |
|  2 | WebSearch (general form / Chebotarev)| "subgroup containing all Frobenius classes is whole Galois group Chebotarev density consequence"   | yes  | Subgroup containing all Frobenius **conjugacy classes** = `G`; density `#C/#G` forces it | Lenstra–Stevenhagen, Wikipedia Chebotarev, MIT 18.785 LectureNotes28 — direct corollary of CDT |
|  3 | WebSearch (named-after / reference)| "Neukirch Marcus 'Frobenius elements generate' Galois group corollary Chebotarev surjective Artin map" | yes  | "By Chebotarev the Artin map is surjective"; **Neukirch Ch. III/VII Cor. 2.10** cited | Kedlaya artin.pdf, MIT LectureNotes7, Artin reciprocity (Wikipedia) |
|  4 | ChatGPT MCP                      | full standard-form / generality / weak-vs-strong / proof-method question (self-contained)               | **n/a** | — | MCP **down** in this environment (Codex exec failed); recorded n/a per task brief, compensated by channels 1–3 + 6–10 |
|  5 | Local references                 | `refs/Chebotarev/`, `.mathlib-quality/references/` for the project                                      | **n/a** | (no refs dir) | `refs/` absent in this checkout; `.mathlib-quality/references/` does not exist — recorded n/a |
|  6 | nLab                             | "Chebotarev density theorem" / "Frobenius element"                                                      | yes  | CDT ⇒ Frobenius elements equidistribute over conjugacy classes; surjectivity of Frobenius map onto `G` | standard nLab framing; concept is classical, not novel |
|  7 | nCatLab (categorical)            | —                                                                                                      | **n/a** | — | Not a categorical concept; no higher-categorical reformulation at stake |
|  8 | Stacks Project (alg geom)        | "Chebotarev" / "Frobenius generate" decomposition group                                                | **n/a** | — | Stacks covers étale-fundamental-group Frobenius but not this analytic-density number-field corollary; not the relevant venue |
|  9 | MathOverflow / Math.SE           | "Frobenius generate Galois group" / "subgroup contains all Frobenius" generality                        | yes  | Consensus: trivially-true *general-G* form needs the **whole conjugacy class** (`Frob_𝔭 ⊆ H`); single-representative form needs `G` abelian (else `H` non-normal counterexamples) | confirms the weak/strong split below |
| 10 | recent arXiv (last 5 yr)         | "Chebotarev density Frobenius generate" effective / function-field                                     | yes  | effective/short-interval CDT refinements (arXiv 1703.08194, 1810.06201, 1404.6345) — all reprove the *same* generation corollary | the corollary itself is textbook; arXiv work is on effectivity, not the statement |

Protocol pass check: WebSearch ran **3** distinct queries at different generality levels (specific
abelian form / general-conjugacy-class form / named-after+reference) ✓; ChatGPT MCP recorded n/a with
reason (down) ✓; local refs n/a with reason (absent) ✓; nLab checked ✓; nCatLab / Stacks recorded n/a
with reason ✓; MathOverflow + arXiv checked ✓.

### Literature summary (Phase 3)

Concept identified as: **"Frobenii of unramified primes generate the Galois group"** — the
subgroup-membership corollary of the **Chebotarev density theorem** (a.k.a. the surjectivity of the
Artin/Frobenius map). Standard references: **Neukirch, *Algebraic Number Theory*, Ch. VII (CDT) /
Ch. III Cor. 2.10**; Marcus, *Number Fields*; Janusz; Lang, *ANT*; MIT 18.785 Lecture Notes 7 & 28;
Lenstra–Stevenhagen survey.

Sources agree on the standard form: **yes**, and they agree on the canonical *general* statement:

> Most general standard form: For **any** finite Galois `L/K` (G need **not** be abelian), if a
> subgroup `H ≤ G` contains, for every unramified prime `𝔭`, the **entire** Frobenius conjugacy
> class `Frob_𝔭` (equivalently, at least one Frobenius and `H` is normal), then `H = G`. Proof: the
> set of primes with `Frob_𝔭 ⊆ C` has Dirichlet density `#C/#G > 0` for every class `C`, so every
> class meets `H`; the classes cover `G`, hence `H = G`.

Generality dimensions where the literature varies:
- **Abelian vs general G**: the *general-G* statement is canonical, **but it must quantify over the
  whole conjugacy class** (`Frob_𝔭 ⊆ H`), or equivalently assume `H` normal. With only a *single
  representative* `.out ∈ H` and no abelian/normal hypothesis, the statement is **false** (a
  non-normal `H` can contain one Frobenius per prime without containing the class). The single-
  representative form is correct **precisely when G is abelian** (classes are singletons). The
  project's form is exactly this **weak form**: abelian + `.out`.
- **Proof method**: the textbook proof is via **Chebotarev density** (positive density ⇒ nonempty).
  The project deliberately uses a **CFT-free zeta-asymptotic** proof instead (comparing
  `Σ N𝔭^{-s} ~ log(1/(s-1))` for `K` and the fixed field). This is a known alternative route
  (it is essentially the "first inequality" / split-prime-counting argument), not a new theorem.

Disagreement with the literature: **none on content.** The project's statement is a *correct
specialisation* (abelian, single representative) of the canonical theorem, with a non-standard but
valid proof. The docstring (L580–587) explicitly and accurately documents this weakening.

## Generality analysis — `Chebotarev.subgroup_eq_top_of_forall_frobenius_mem`

Literature-standard form (from Phase 3): general finite Galois `L/K`, `H` containing the **whole
conjugacy class** `Frob_𝔭` for every unramified `𝔭` (no abelian hypothesis), concludes `H = ⊤`.

| # | Parameter / hypothesis                          | Current Lean form                              | Literature-standard form                              | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------------------------|------------------------------------------------|--------------------------------------------------------|---------------------|---------------------------------|
| 1 | `[IsMulCommutative Gal(L/K)]`                    | `G` abelian                                    | **no abelian hypothesis** (general `G`)                | **NO — not for this hypothesis shape** | Dropping abelian-ness is *only* valid if hypothesis #2 is simultaneously strengthened to the whole class; with `.out` alone the abelian hypothesis is load-bearing (docstring L581–587). |
| 2 | `hH : … (frobeniusClass 𝔭).out ∈ H`             | single class **representative** `.out ∈ H`     | **whole class** `∀ σ ∈ Frob_𝔭, σ ∈ H` (or `H` normal)  | (it is already the *weaker* hypothesis) | The literature uses the *stronger* hypothesis (whole class). The user's `.out`-only hypothesis is weaker, which is why it forces the abelian side-condition. |
| 3 | `K L` number fields, `IsGalois`, finite          | number fields                                  | number fields (CDT is a number-field theorem)          | NO                  | The zeta-asymptotic proof and CDT both live over number fields; this is the correct base generality. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (along the abelian axis), but with a
*coupled* hypothesis trade-off that makes the naive "just drop abelian" weakening **unsound**.

Number of weakening opportunities found: **1 coupled axis** — generalise to non-abelian `G` *only* by
simultaneously replacing the `.out ∈ H` hypothesis with a full-conjugacy-class hypothesis
`Frob_𝔭 ⊆ H`. This is not a free mechanical weakening; it is a genuine restatement requiring the
class-level Frobenius and a class-covers-`G` argument (and a different split-prime-multiplicity
bookkeeping in the zeta proof).

Proposed restatement (the literature-standard general form):

```lean
theorem subgroup_eq_top_of_forall_frobeniusClass_subset
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (H : Subgroup Gal(L/K))
    (hH : ∀ 𝔭 : Ideal (𝓞 K), ∀ _ : 𝔭.IsPrime, 𝔭 ≠ ⊥ → UnramifiedIn K L 𝔭 →
      ∀ σ : L ≃ₐ[K] L, ConjClasses.mk σ = frobeniusClass K L 𝔭 → σ ∈ H) :
    H = ⊤ := by
  sorry -- needs the class-level Chebotarev/zeta argument; current abelian proof does NOT survive verbatim
```

Cost of restatement: **EXPENSIVE** — the project's proof goes through the *chosen representative*
only; the general form needs the whole-class statement and the split-completely transfer for the
general `[F:K]`-fold multiplicity, which the docstring (L584–587) states the current machinery does
**not** provide. This is genuinely new math, not a mechanical rewrite.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                         | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|--------------------------------------------------------------------------------------------------|----------|------------------------|---------------------------------|
|  1 | "let X be a foo" → typeclass/instance instead of bundled hypothesis?                             | no | — | Hypotheses are already typeclasses (`IsGalois`, `NumberField`, `IsMulCommutative`); `hH` is irreducibly a `∀`-hypothesis. |
|  2 | sequences/metric → filters/topological?                                                          | no | — | No sequence/metric in the *statement* (the zeta proof uses filters already, internally). |
|  3 | construct an object where a universal-property class would characterise it?                      | no | — | This is a theorem, not a construction. |
|  4 | set-with-closure-predicate → bundled-substructure?                                               | no | — | `H` is already `Subgroup`, a bundled type; conclusion is `H = ⊤`. |
|  5 | vector-space/metric/field-specific → weaken typeclass hierarchy?                                  | no | — | Number-field-specific by nature (CDT); cannot weaken below number fields. |
|  6 | 1-categorical → higher/∞-categorical?                                                            | no | — | Not categorical. |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive group/monoid?                                        | no | — | No concrete index in the statement. |

Modern idiom available: **no.** The only real generalisation is the *literature* one (full conjugacy
class, drop abelian) captured in 4b — not a Bourbaki-2.0 idiom swap. One-line reason: the statement
is already in mathlib-idiomatic form (`Subgroup`, `IsGalois`, typeclass hypotheses); the gap is purely
the abelian/representative specialisation, which is a *mathematical* weakening, not a reformulation.

## Diamond / defeq risk — Phase 4.5

n/a — declaration kind is `theorem`. (No definitional equalities or typeclass-search paths
introduced.)

## Mathlib search-status: `Chebotarev.subgroup_eq_top_of_forall_frobenius_mem`

[A] Lean-Finder       (tool unavailable in env)                                  **n/a: Lean-Finder MCP not present**
[B] Loogle            (`lean_loogle` unavailable; tried Loogle-via-web)          **n/a: lean_loogle tool not loaded; web fallback returned only Galois.Basic docs, no match**
[C] LeanSearch        (`lean_leansearch` unavailable)                            **n/a: tool not loaded**
[D] Grep mathlib src  `ebotarev` (whole tree); `frobeniusClass`; `density` (NumberTheory); `Frobenius.*(generat|surj|top|span|closure)`; `arithFrobAt`; `card_aut_eq_finrank`; `finrank_fixedField_eq_card`; `card_eq_iff_eq_top` | **hits only for the plumbing, none for the result** |
[E] Name pattern      `subgroup_eq_top_of`, `eq_top_of_forall`, `fixedField_eq_top`, `eq_top_iff_card`, `Subgroup.eq_top_of` | **no Frobenius/Chebotarev-flavoured eq_top lemma** |

Searched for both:
- the user's current form (abelian, `.out ∈ H` ⇒ `H = ⊤`): **no hit**
- the literature-standard general form (whole class ⇒ `H = ⊤`, i.e. Chebotarev surjectivity): **no
  hit** — and crucially **there is no Chebotarev density theorem in mathlib at all** (`grep -rlin
  "ebotarev"` over the whole Mathlib tree returns **nothing**; `grep "density"` over
  `Mathlib/NumberTheory` returns **nothing** — the nearest analytic-density result is
  `Mathlib/NumberTheory/LSeries/PrimesInAP.lean`, Dirichlet's theorem on primes in arithmetic
  progression, which is a *different* statement and does not give Frobenius/Galois density).

Plumbing that mathlib DOES have (used by the top two lines of the project proof):
- `Subgroup.card_eq_iff_eq_top` (`Mathlib/Algebra/Group/Subgroup/Finite.lean:130`)
- `IsGalois.card_aut_eq_finrank` (`Mathlib/FieldTheory/Galois/Basic.lean:109`)
- `IntermediateField.finrank_fixedField_eq_card` (`Mathlib/FieldTheory/Galois/Basic.lean:222`)
- `Module.finrank_mul_finrank`
- `arithFrobAt` (`Mathlib/RingTheory/Frobenius.lean:258`) — the per-prime Frobenius *exists* in mathlib…
- …but `frobeniusClass` (the conjugacy class, dependency of the hypothesis) is **project-defined**
  (`projects/Chebotarev/CebotarevDensity/Frobenius.lean:188`), and the substantive bound
  `finrank_fixedField_le_one_of_forall_frobenius_mem` is **project-only**.

Concluded: **not in mathlib** (all available methods exhausted — direct grep over the full source is
authoritative here — plus the literature-standard general form). The result, the Chebotarev density
theorem it specialises, and the analytic-density machinery the proof needs are all absent from mathlib.

## Call sites — `Chebotarev.subgroup_eq_top_of_forall_frobenius_mem`

Internal use count: **K = 0** (within the project, excluding the declaring file and excluding the
distinct decl `…_of_coprime`). The bare-name grep over `projects/` returns only: the module docstring
(L22), a prose mention (L336), the docstring of its coprime sibling (L553), and its own definition
(L592). **No code consumer.**

External-to-file callers: **0.**

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| (none — `subgroup_eq_top_of_forall_frobenius_mem` is invoked nowhere in code) | — |

Inline-derivation grep (is the equivalent re-derived elsewhere?):
- The *consumer* of this circle of ideas, `ZetaProduct.lean:1053`, calls
  `subgroup_eq_top_of_forall_frobenius_mem_of_coprime` (the **coprime** variant) **directly** — i.e.
  the project bypasses the non-coprime `…_mem` theorem entirely and uses its sibling. So the actual
  workhorse is `…_of_coprime`; `…_mem` is a *thin convenience wrapper* (`m = 1` specialisation) that
  currently has **no caller**.

Composability signal (per the call-sites table in the verdicts doc): **K = 0 with the equivalent
content live at a sibling decl** → the lemma is a wrapper consumers bypass. This *on its own* leans
NO; but see Phase 7 — the wrapper bypass is about *which project lemma is canonical*, not about
mathlib having the content.

## Composition check (Phase 6)

Can `subgroup_eq_top_of_forall_frobenius_mem` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: `rw [← Subgroup.card_eq_iff_eq_top]; rw [card_aut_eq_finrank, finrank_fixedField_eq_card]; exact <bound>`
- Mathlib decls used: `Subgroup.card_eq_iff_eq_top`, `IsGalois.card_aut_eq_finrank`,
  `IntermediateField.finrank_fixedField_eq_card`, `Module.finrank_mul_finrank`.
- Result: **fails** — these only rewrite `H = ⊤` into the goal `[fixedField H : K] = 1`. The final
  `exact <bound>` requires `finrank_fixedField_le_one_of_forall_frobenius_mem`, which is the **entire
  Chebotarev/zeta-asymptotic argument** (hundreds of lines of project code: `primeIdealZetaSum`
  asymptotics, split-prime multiplicity, `le_of_tendsto_of_tendsto`). That is **not** a mathlib decl
  and **not** a ≤3-call composition.
- Notes: the *outer shell* (2 rewrites) is composable from mathlib; the *content* is not.

Attempt 2: derive from a mathlib Chebotarev density theorem.
- There is **no** Chebotarev density theorem in mathlib (Phase 5). Nothing to compose from.

Conclusion: **NOT-COMPOSABLE.** Mathlib supplies the Galois-correspondence plumbing but none of the
substantive analytic-number-theory content; no ≤3-call mathlib composition yields the result.

## Verdict: `Chebotarev.subgroup_eq_top_of_forall_frobenius_mem`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): canonical theorem ("Frobenii generate `Gal(L/K)`", Chebotarev
  corollary, Neukirch VII / Cor. III.2.10, Marcus, MIT 18.785) — but the *canonical* form is
  general-`G` + **whole conjugacy class**; the project's form is the **abelian + single-representative
  `.out`** weak specialisation.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD**; the one generalisation axis
  (drop abelian) is **coupled** to strengthening the hypothesis to the full class, cost **EXPENSIVE**
  (new math; current proof does not survive — confirmed by the author's own docstring L580–587).
- Mathlib search (Phase 5): **not in mathlib**, and neither is the Chebotarev density theorem nor any
  analytic-density-in-number-theory machinery the proof rests on.
- Composition check (Phase 6): **NOT-COMPOSABLE** (mathlib gives the 2-rewrite shell only; the content
  is a large project argument).

**Rationale:**

The mathematical content is unambiguously mathlib-worthy *in principle*: "Frobenius elements of
unramified primes generate the Galois group" is a textbook theorem, mathlib has no Chebotarev density
theorem, and this CFT-free zeta-asymptotic route is a legitimate and valuable way to obtain it. So
this is not a NO. But two facts block a clean YES and make the call a human judgement:

1. **The form is the abelian, single-representative *weak* form, and the standard form is the
   general-`G` whole-conjugacy-class form.** This is exactly the `YES-but-generalise-first` shape —
   except the generalisation is **EXPENSIVE** (genuinely new math, the proof does not survive, per the
   author's own note). Per the skill's own rule, "the more general form is too expensive, so ship the
   narrow one" is **not** a self-resolving downgrade — it is a question for the user. Whether to
   upstream the abelian form now (as a deliberately-scoped lemma, with the general form as future
   work) or to hold for the general form is a taste/policy call.

2. **The theorem is non-load-bearing in the project (`K = 0` callers); the actual workhorse is its
   sibling `…_of_coprime`**, which `ZetaProduct.lean` calls directly. So even the *project-local*
   status of this exact decl (keep as a convenience wrapper vs. inline the `m = 1` specialisation) is
   unsettled — and that bears on whether it is the right grain to upstream at all.

Neither blocker is resolvable from the evidence alone. The content says "yes eventually"; the
generality gap + EXPENSIVE cost + zero-consumer wrapper status say "ask first".

**Numbered questions (≤5):**

1. **Generality/cost trade-off (the central question):** the standard mathlib target is the
   *general-`G`, whole-conjugacy-class* statement (`Frob_𝔭 ⊆ H ⇒ H = ⊤`), which your own docstring
   says the current machinery does **not** prove (the `.out`-only proof needs `G` abelian). Do you
   want to (a) upstream the **abelian** form now as an explicitly-scoped lemma with the general form
   flagged as future work, or (b) **hold** until the general (whole-class) form is proved and upstream
   that instead?
2. **Prerequisite gap:** mathlib has **no Chebotarev density theorem** and **no analytic density in
   number theory** (only Dirichlet's `PrimesInAP`). Upstreaming this means upstreaming the
   `primeIdealZetaSum` asymptotic infrastructure too. Is landing that analytic infrastructure in
   mathlib in scope, or is the intent to keep this whole circle project-local for now?
3. **Right decl to upstream:** the workhorse is `…_of_coprime` (it has the real consumer); `…_mem` is
   a `m = 1` convenience wrapper with **no caller**. If anything goes to mathlib, should it be the
   *coprime* lemma (more general), with `…_mem` derived as a corollary — i.e. is `…_mem` even the
   right target?
4. **Naming:** the project name `subgroup_eq_top_of_forall_frobenius_mem` reads well, but a mathlib
   PR would likely want it in a `NumberField`/`Chebotarev` namespace and possibly phrased via the
   Artin-map surjectivity. Is the current statement shape (subgroup-membership ⇒ `⊤`) the form you
   want upstream, or the Artin-map-surjective form?

**Next action:** user answers 1–4; re-run `/mathlibable Chebotarev.subgroup_eq_top_of_forall_frobenius_mem`
to resolve. Likely outcomes:
- (1a) + keep narrow → flips to **YES-but-generalise-first** (target = general whole-class form),
  shipping the abelian form now with the generalisation flagged, *contingent* on Q2 (the analytic
  prerequisite) being in scope.
- (1b) or Q2 "keep project-local" → remains effectively **not-now** for mathlib (the prerequisite
  Chebotarev/zeta infrastructure must land first); revisit after that.
- Q3 "upstream `…_of_coprime` instead" → re-run `/mathlibable` on that decl as the real target.

---

## Next step

User answers the four numbered questions (especially Q1: ship the abelian form now vs. hold for the
general whole-conjugacy-class form, given the EXPENSIVE cost and the missing mathlib Chebotarev/density
prerequisite), then re-run `/mathlibable` to commit to a verdict.

---

### Sources (literature)
- William Stein, *Algebraic Number Theory* notes — Frobenius elements: https://wstein.org/papers/ant/html/node54.html
- MIT 18.785 Lecture Notes 7 (Galois extensions, Frobenius elements, Artin map): https://math.mit.edu/classes/18.785/2021fa/LectureNotes7.pdf
- MIT 18.785 Lecture Notes 28 (Global CFT, Chebotarev density): https://math.mit.edu/classes/18.785/2017fa/LectureNotes28.pdf
- Kedlaya 18.785 — Frobenius elements of Galois groups: https://kskedlaya.org/18.785/artin.pdf
- Lenstra, *The Chebotarev Density Theorem*: https://websites.math.leidenuniv.nl/algebra/Lenstra-Chebotarev.pdf
- Stevenhagen–Lenstra, *Chebotarëv and his density theorem*: https://pub.math.leidenuniv.nl/~lenstrahw/papers/cheb.pdf
- Chebotarev density theorem — Wikipedia: https://en.wikipedia.org/wiki/Chebotarev_density_theorem
- Artin reciprocity — Wikipedia: https://en.wikipedia.org/wiki/Artin_reciprocity
- (standard texts: Neukirch *ANT* Ch. III Cor. 2.10 / Ch. VII; Marcus *Number Fields*; Janusz; Lang *ANT*)
