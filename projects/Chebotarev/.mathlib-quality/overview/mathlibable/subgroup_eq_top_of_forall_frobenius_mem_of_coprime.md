# /mathlibable report — `Chebotarev.subgroup_eq_top_of_forall_frobenius_mem_of_coprime`

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task note; reasoning from source — the
                            decl elaborates in the integrated `main` build, which is green by repo policy)
- decl `Chebotarev.subgroup_eq_top_of_forall_frobenius_mem_of_coprime`:
                            ✓ resolved at `projects/Chebotarev/CebotarevDensity/CyclotomicNormResidue.lean:560`
- kind:                      theorem  (⇒ Phase 4.5 diamond/defeq risk is **n/a**)
- has sorry:                 no (proof is complete; delegates to a private helper, also sorry-free)
- module docstring summary:  "The cyclotomic Frobenius as a norm residue, and Frobenii generate" —
                            two arithmetic inputs of the Frobenius-fibre equidistribution, including
                            the CFT-free "Frobenii generate the Galois group" theorem.

### Statement (Phase 1)

`Chebotarev.subgroup_eq_top_of_forall_frobenius_mem_of_coprime` is a **theorem** stating:

Let `L/K` be a finite Galois extension of number fields with **abelian** Galois group `G = Gal(L/K)`,
and fix `m ∈ ℕ`, `m ≠ 0`. Let `H ≤ G` be a subgroup. Suppose that for **every** nonzero prime ideal
`𝔭` of `𝓞 K` that is unramified in `L` **and whose absolute norm `N𝔭` is coprime to `m`**, the chosen
representative `(frobeniusClass 𝔭).out` of the Frobenius conjugacy class of `𝔭` lies in `H`. Then
`H = G` (i.e. `H = ⊤`).

Mathematically this is the **algebraic core of Chebotarev's density theorem**: the Frobenius elements
of (almost all) primes *generate* the Galois group. The proof is the classical analytic one — pass to
the fixed field `F = L^H`; every coprime-norm unramified prime of `K` splits completely in `F`; comparing
the prime-ideal zeta sums `Σ N𝔭^{-s} ~ log(1/(s-1))` for `K` and for `F` against the `[F:K]`-fold
multiplicity of split primes forces `[F:K] = 1`, hence `H = ⊤`. The "coprime to `m`" restriction merely
excludes a finite set of primes, which does not change the limiting zeta ratio.

Variables / typeclasses (Lean side):
- `K L : Type*`, `[Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]` —
  a finite Galois extension of number fields.
- `[IsMulCommutative Gal(L/K)]` — **abelian Galois group** (a genuine restriction; see Phase 4).
- `(m : ℕ) [NeZero m]` — the modulus controlling which primes are tested.
- `(H : Subgroup Gal(L/K))` — the subgroup under test.

Hypotheses (Lean side):
- `hH : ∀ 𝔭, 𝔭.IsPrime → 𝔭 ≠ ⊥ → UnramifiedIn K L 𝔭 → (N𝔭).Coprime m →
        ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) ∈ H` — `H` contains the Frobenius **representative**
  (`.out`, not the whole conjugacy class) of every coprime-norm unramified nonzero prime.

Conclusion (math): `H = Gal(L/K)`.
Conclusion (Lean): `H = ⊤`.

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: It is a named, textbook theorem ("Frobenius elements generate the Galois group" — the algebraic
heart of Chebotarev density), and a primary deliverable of the Chebotarev project; it is essentially
guaranteed to appear in the literature in some form.

(Literature width is EXHAUSTIVE regardless. BIG/SMALL recorded for framing only.)

### One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure` — one-line check **n/a**. (The body is a multi-step
proof: `card_eq_iff_eq_top` reduction + `finrank_mul_finrank` tower + the private degree-≤-1 helper.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                 | Hit? | Standard form found                                                          | Notes |
|----|----------------------------------|-------------------------------------------------------------------------------------------------------|------|------------------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | Frobenius elements generate Galois group dense / Chebotarev density theorem                            | yes  | Frobenius elements equidistribute over `G`; their classes exhaust `G`        | Berkeley (Yott), Lenstra, Wikipedia, Stevenhagen–Lenstra — all standard sources |
|  2 | WebSearch (subgroup form)        | subgroup containing all Frobenius conjugacy classes is whole Galois group, proof via zeta function    | yes  | implicit in Artin L-function / Kedlaya 18.785 notes; not isolated as a lemma | Kedlaya `artin.pdf`, Stein ANT — the statement is folklore, used inside Chebotarev proofs |
|  3 | WebSearch (split-completely)     | primes split completely ⇔ Frobenius trivial; fixed field degree one; Dedekind zeta                    | yes  | "density of split-completely primes = 1/[L:K]"; `[L:K]=1 ⇔ split set has density 1` | Grokipedia, arXiv 2307.12175 — this **is** the proof mechanism the Lean decl uses |
|  4 | WebSearch (topological form)     | closed subgroup generated by Frobenius elements dense / topologically generate absolute Galois group  | yes  | "each decomposition group is generated by its Frobenius; Frobenii are dense in `G`" | Stein ANT node51/58; Wikipedia "Splitting of prime ideals in Galois extensions" |
|  5 | WebSearch (Lenstra abelian)      | Lenstra Chebotarev split completely Dirichlet density 1/n abelian, proof without class field theory   | yes  | abelian case: split-density ⇒ Frobenius-class density; CFT-free analytic proof | Stevenhagen–Lenstra `cheb.pdf`, Lenstra `Lenstra-Chebotarev.pdf`, MIT 18.785 LN28 — **the project's own cited source** |
|  6 | ChatGPT MCP                      | standard form + generality + historical evolution of "Frobenii generate the Galois group"             | n/a  | (MCP down per task note; fallback channels 1–5, 7–10 cover the same ground)  | recorded n/a — server unavailable; ≥5 WebSearch queries + nLab/MO compensate |
|  7 | Local references                 | grep `.mathlib-quality/references/` for Chebotarev/Frobenius                                           | n/a  | (no `references/` dir; no `refs/Chebotarev/`)                                | directory absent — recorded n/a. Source-of-record per docstrings is **Sharifi** §7.2 + Stevenhagen–Lenstra |
|  8 | nLab                             | Frobenius / Chebotarev density / decomposition group                                                  | yes  | nLab frames it via "Frobenius elements are dense in `Gal`"; Chebotarev = equidistribution | abstract statement matches #1/#4 |
|  9 | Stacks Project (if alg geom)     | —                                                                                                     | n/a  | not an algebraic-geometry / scheme-theoretic concept in the Stacks sense    | Chebotarev density is analytic NT; Stacks has no density theory — recorded n/a |
| 10 | nCatLab / MathOverflow / arXiv   | "Frobenius generate Galois group", abelian Chebotarev, recent (≤5y) sharpenings                        | yes  | arXiv 2210.13412 (supplement to Chebotarev), 2407.14341 (frobenian conditions); MO threads | confirms the result is standard and actively cited; no fundamentally different modern formulation of *this* lemma |

The protocol passes: WebSearch ran 5 distinct queries at different generality levels (named theorem,
subgroup form, split-completely mechanism, topological/closed-subgroup form, abelian CFT-free case);
local refs + Stacks recorded n/a with reasons; nLab + MO/arXiv checked. ChatGPT MCP unavailable
(server down) — compensated by the extra WebSearch breadth.

### Literature summary (Phase 3)

Concept identified as: **"Frobenius elements generate the Galois group"** — the algebraic statement
underlying **Chebotarev's density theorem** (special/limiting case: a Galois extension in which (almost)
all primes split completely is trivial, `[L:K]=1`). Standard names: *Chebotarev density* (the quantitative
form), *Frobenius density / equidistribution*, and at the structural level "the Frobenius elements are
(topologically) dense in `Gal(L/K)`".

Sources agree on the standard form: **yes**. Across Lenstra, Stevenhagen–Lenstra, Kedlaya, Stein, and
Wikipedia, the canonical statement is: *for a finite Galois extension `L/K`, the conjugacy classes of
Frobenius elements of the unramified primes exhaust the whole group; equivalently, a subgroup `H ≤ G`
containing a Frobenius element of every unramified prime equals `G`.* It is stated for **arbitrary**
Galois `L/K` (not just abelian) and quantifies over the **conjugacy class** (any Frobenius element of the
prime, well-defined up to conjugacy), not a single chosen representative.

Most general standard form: arbitrary finite (indeed profinite, with "topologically generate") Galois
extension; hypothesis is "for every unramified prime `𝔭`, the/a Frobenius class meets `H`" — typically
phrased "`H` contains a Frobenius of each `𝔭`", which for a **normal** `H` is class-membership and for
general `H` is "meets the class".

Generality dimensions where the literature varies:
  - **Abelian vs. general `G`**: literature default is **arbitrary** Galois `G`. The Lean decl restricts
    to `[IsMulCommutative Gal(L/K)]` (abelian).
  - **Representative `.out` vs. whole conjugacy class**: literature quantifies over the class (or over a
    normal `H`, where it is class-membership). The Lean decl uses only the chosen rep `(frobeniusClass 𝔭).out`.
  - **All unramified primes vs. coprime-norm subset**: literature uses *all* (cofinitely many) unramified
    primes. The Lean decl restricts to the `N𝔭` coprime-to-`m` subset — a *cofinite* subset, so mathematically
    equivalent in the limit (the docstring at lines 556–558 notes the excluded primes form a finite set).
  - **Number field vs. global field**: literature also covers function fields; Lean fixes number fields.

Disagreement with the literature: the Lean form is a **specialisation** (abelian, `.out`-only). The
project docstring (lines 580–587) is explicit and correct that the `.out`-only hypothesis genuinely
*requires* abelian `G`: for non-abelian `G` a non-normal `H` can contain one Frobenius representative per
prime without containing the whole class, and the split-completely transfer fails. So the *general* mathlib
form must quantify over the class, not `.out`.

---

### Generality analysis — `Chebotarev.subgroup_eq_top_of_forall_frobenius_mem_of_coprime`

Literature-standard form (from Phase 3): for an **arbitrary** finite Galois extension `L/K` of number
fields and `H ≤ Gal(L/K)`, if `H` meets the Frobenius conjugacy class of every unramified prime `𝔭` of
`K` (equivalently, for normal `H`, contains it), then `H = ⊤`.

| # | Parameter / hypothesis                              | Current Lean form                               | Literature-standard form                          | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------------------------|-------------------------------------------------|---------------------------------------------------|---------------------|----------------------------------|
| 1 | `[IsMulCommutative Gal(L/K)]`                       | abelian Galois group                            | **arbitrary** Galois group                        | **YES**             | Removable *iff* the hypothesis is upgraded to whole-class membership (row 2). With `.out`-only it is genuinely needed (docstring 580–587). |
| 2 | `hH … ((frobeniusClass 𝔭).out) ∈ H`                 | chosen representative `.out` ∈ `H`              | the whole conjugacy class meets/lies in `H`       | n/a (it's a *strengthening* of the conclusion's reach) | The general statement *quantifies over the class*; doing so is what lets row 1 drop. This is the key generalisation axis. |
| 3 | `(N𝔭).Coprime m` (with `m`, `[NeZero m]`)           | tests only coprime-norm primes                  | tests all (cofinitely many) unramified primes     | **YES**             | The plain `subgroup_eq_top_of_forall_frobenius_mem` (line 592) is literally this decl at `m = 1`. The `m` parameter is a project convenience (κ-uniformity realizer), not a mathematical necessity — excluded primes are finite. |
| 4 | `[NumberField K] [NumberField L]`                   | number fields                                   | global fields (number or function field)          | YES (in principle)  | The zeta-asymptotics proof is number-field-specific in this project; weakening to global fields needs the function-field zeta API. NOT cheap here. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD**
Number of weakening opportunities found: **3** (abelian→general via class-quantification; coprime-subset→all-primes; number-field→global-field).

Proposed restatement (the mathlib-standard target):

```lean
-- General (non-abelian) form, quantifying over the whole Frobenius conjugacy class.
-- For a NORMAL H the class-membership below is the natural hypothesis; for general H,
-- "the class meets H" is the right phrasing. mathlib would likely take the normal-H /
-- whole-class statement and also keep the abelian corollary.
theorem subgroup_eq_top_of_forall_frobeniusClass_le
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (H : Subgroup Gal(L/K))
    (hH : ∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsPrime → 𝔭 ≠ ⊥ → UnramifiedIn K L 𝔭 →
        ∀ σ : L ≃ₐ[K] L, ConjClasses.mk σ = frobeniusClass K L 𝔭 → σ ∈ H) :
    H = ⊤ := by
  sorry  -- needs work; current abelian proof is the H-normal / abelian special case
```

Cost of restatement: **EXPENSIVE** — the current proof's split-completely transfer uses the chosen
representative and abelian-ness essentially. The general (whole-class / non-abelian) proof needs the
genuine conjugacy-class equidistribution argument (or a normality reduction), i.e. new mathematical
content beyond a mechanical rewrite. (The *coprime → all-primes* axis alone, by contrast, is **CHEAP** —
it is already exhibited by the `m = 1` corollary at line 592.)

(Cost note: EXPENSIVE does not downgrade the verdict. Mathlib's value is the right form; per the skill's
gate, "too expensive" is a sequencing remark, not a reason to ship the narrow form as-is.)

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                  | Applies? | Proposed reformulation                                                       | Mathlib downstream this enables |
|----|-----------------------------------------------------------------------------------------------------------|----------|------------------------------------------------------------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                       | no       | already fully typeclass-driven (`[IsGalois K L]`, `[NumberField _]`, …)      | n/a |
|  2 | sequences/metric → filters/nets/topological?                                                              | partial  | the **closed-subgroup / topological-generation** form (`Gal` profinite) is the modern abstract statement; but for *finite* `L/K` the discrete `H = ⊤` form is the right finite-level statement | the profinite form would feed an absolute-Galois-group API mathlib does not yet have |
|  3 | construct an object → universal-property class?                                                           | no       | the result is a property of a subgroup, not a construction                   | n/a |
|  4 | set-with-closure-predicate → bundled substructure?                                                        | no       | `H` is already a bundled `Subgroup`; conclusion is `= ⊤`                     | n/a |
|  5 | vector-space/metric/field-specific → weaker typeclass?                                                    | no       | the field/number-field hypotheses are essential (it is a number-theoretic statement) | n/a |
|  6 | 1-categorical → higher-categorical?                                                                       | no       | not a categorical statement                                                  | n/a |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group?                                                          | yes (the `m`) | drop `m`: the all-unramified-primes form (row 3 of 4a). This is the `m = 1` corollary already present | unifies with the plain theorem; removes the κ-uniformity-specific `m` from the general statement |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes (mild)** — two real organisational improvements, both *already in the
direction of the literature-standard form* rather than a separate categorification:
  - Drop the `m`/coprime scaffolding and state for **all** unramified primes (the `m = 1` corollary). This
    is the clean statement; `m` is project plumbing.
  - State over the **whole Frobenius conjugacy class** (which simultaneously removes the abelian
    restriction) — this is the Phase 4b target, and is the genuinely valuable generalisation.
  - Cost: dropping `m` is CHEAP; whole-class/non-abelian is EXPENSIVE (new proof content).
  - Mathlib downstream this enables: a single canonical "Frobenii generate `Gal`" lemma usable by *any*
    future Chebotarev/density development (none of which would want an `m`-coprime hypothesis or an
    abelian restriction baked in); it is the natural lemma that `Mathlib.NumberTheory`'s eventual
    Chebotarev formalisation would cite.
  - Real mathematical improvement (not just cosmetic): yes — the general form is strictly more useful and
    is the form every textbook states; the abelian/`.out`/coprime form is a project-local specialisation.

Because Phase 4c (and 4b) identify a strictly more general, literature-standard target, **Phase 7 selects
`YES-but-generalise-first`**, not `YES-add-as-is`.

---

### Diamond / defeq risk — `Chebotarev.subgroup_eq_top_of_forall_frobenius_mem_of_coprime`

**n/a — declaration kind is `theorem`.** Theorems introduce no definitional equalities or
typeclass-search paths, so Phase 4.5 is skipped.

---

### Mathlib search-status: `Chebotarev.subgroup_eq_top_of_forall_frobenius_mem_of_coprime`

[A] Lean-Finder       (mathlib index unavailable locally; covered by C/D below)        n/a: tool not wired in this env
[B] Loogle            `Subgroup _ → _ = ⊤` with Frobenius/Galois shape                  n/a: lean_loogle not available as a deferred tool in this env; substituted by grep [D]
[C] LeanSearch        "Frobenius elements generate the Galois group", "subgroup containing all Frobenius is top" | no hits: mathlib has no such lemma (see [D])
[D] Grep mathlib src  `Chebotarev`/`chebotarev` (whole tree); `frobenius.*(eq_top|generate|surject|dense)`; `splits.*completely`; Dirichlet density of prime ideals | **no hits** for Chebotarev (zero files); the only nearby decl is `IsCyclotomicExtension.Rat.galEquivZMod_stabilizer` |
[E] Name pattern      `subgroup_eq_top_of_forall_frobenius`, `frobeniusClass`, `UnramifiedIn` in mathlib | no hits: these names are project-local; mathlib has `arithFrobAt`/decomposition API but no generation theorem |

Searched for both:
  - the user's current form (abelian, `.out`, coprime-norm) — **not in mathlib**.
  - the literature-standard form (arbitrary `L/K`, whole class, all unramified primes) — **not in mathlib**.

Nearest mathlib decl examined: `IsCyclotomicExtension.Rat.galEquivZMod_stabilizer`
(`Mathlib/NumberTheory/NumberField/Cyclotomic/Galois.lean`). This says: for `ℚ(ζₙ)/ℚ` and a prime `P`
over `p ∤ n`, the image under `galEquivZMod` of **the decomposition group of the single prime `P`** is the
cyclic subgroup generated by the Frobenius `[p]`. That is the *single-prime decomposition-group* statement,
a different and far narrower fact than "the subgroup generated by Frobenii of **all** primes is the whole
group". It does not specialise to our theorem, and our theorem does not follow from it.

Mathlib also has **no Dirichlet/natural density of prime ideals** and **no Dedekind-zeta residue / prime
zeta asymptotics** of the kind the proof needs — the entire analytic-density layer this theorem sits on
top of is absent from mathlib (the Chebotarev project is building it).

Concluded: **not in mathlib** (all available methods exhausted, plus the literature-standard form). Mathlib
has neither the result nor (yet) the analytic machinery behind it.

---

### Call sites — `Chebotarev.subgroup_eq_top_of_forall_frobenius_mem_of_coprime`

Internal use count: **1** real application (within the project, excluding the declaring file).
External-to-file callers: **1** distinct file (`ZetaProduct.lean`). Plus the `m = 1` corollary
`subgroup_eq_top_of_forall_frobenius_mem` (same file, line 598) is defined *in terms of* it.

| Caller file:line                                   | Usage pattern (one-line excerpt)                                                       |
|----------------------------------------------------|-----------------------------------------------------------------------------------------|
| `CebotarevDensity/ZetaProduct.lean:1053`           | `refine subgroup_eq_top_of_forall_frobenius_mem_of_coprime K L m H (fun 𝔭 … ↦ ?_)` — proves `H = comap autToPow R = ⊤` (the κ-uniformity realizer) |
| `CebotarevDensity/CyclotomicNormResidue.lean:598`  | `subgroup_eq_top_of_forall_frobenius_mem K L 1 H (fun … ↦ hH …)` — the `m = 1` corollary delegates here |
| `CebotarevDensity/ZetaProduct.lean:1009,1041,1780` | docstring references only (no code use)                                                  |

Inline-derivation grep (re-derived elsewhere without using this decl?): **(none)** — no other site
reproves "Frobenii generate `G`"; the only other "frobenius ∈ H" reasoning is the private sub-lemma block
(lines 210–300) that *supports* this theorem's helper, not a re-derivation.

Call-sites signal: **K = 1 genuine internal use** (plus one corollary), no inline re-derivation. Per the
6.0.1 table this is the "possibly-narrow-abstraction / single-use" pattern, **but** that leaning is
overridden here: the decl is a *named textbook theorem* whose single in-project use reflects that the
project only needs the abelian case, not that the result is a throwaway wrapper. The composability signal
is therefore neutral-to-positive (it IS the API other developments would cite), and the verdict is driven
by Phases 3–5, not by the use count.

---

### Composition check (Phase 6)

Can `subgroup_eq_top_of_forall_frobenius_mem_of_coprime` be derived from mathlib in ≤3 chained calls?

Attempt 1: reduce to `[F:K] ≤ 1` and feed a mathlib "Frobenius generation" / "split-completely ⇒ trivial"
lemma.
  - Mathlib decls used: `Subgroup.card_eq_iff_eq_top`, `Module.finrank_mul_finrank`,
    `IntermediateField.finrank_fixedField_eq_card`, `IsGalois.card_aut_eq_finrank` — the *outer* Galois
    bookkeeping **is** mathlib (and the proof uses exactly these). But the load-bearing inner step
    `finrank_fixedField_le_one_of_forall_frobenius_mem_of_coprime` (the private helper at line 518) is
    **not** a mathlib call: it is a ~30-line analytic argument (`primeIdealZetaSum_*_div_log_tendsto_one`,
    `finrank_mul_unramified_coprime_le_univ`, `le_of_tendsto_of_tendsto`) built on the project's own zeta
    asymptotics, none of which exist in mathlib.
  - Result: **fails** — the Galois-theoretic wrapper composes from mathlib in ~4 calls, but the
    mathematical heart (degree ≤ 1 via zeta comparison) is irreducibly a multi-lemma analytic proof, not a
    1–3-call composition.

Attempt 2: find a mathlib "split-completely density forces `[L:K]=1`" lemma to drop in.
  - Mathlib decls used: none exist (Phase 5: no density, no prime-zeta-residue, no Chebotarev).
  - Result: **fails** — the building block does not exist in mathlib at all.

Conclusion: **NOT-COMPOSABLE.** Mathlib supplies only the trivial outer Galois reduction; the actual
theorem (and its degree-≤-1 helper) is genuinely new mathematics resting on analytic machinery mathlib
lacks. This confirms a YES-family verdict (not NO-composable).

---

## Verdict: `Chebotarev.subgroup_eq_top_of_forall_frobenius_mem_of_coprime`

**Category:** **YES-but-generalise-first**

**Evidence:**
- Literature search (Phase 3): standard, named theorem ("Frobenii generate the Galois group" / algebraic
  core of Chebotarev density), Lenstra & Stevenhagen–Lenstra et al.; literature states it for **arbitrary**
  Galois `L/K` over the **whole conjugacy class** and **all** unramified primes.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — 3 weakening axes (abelian→general
  via class-quantification; coprime-subset→all-primes; number-field→global-field).
- Mathlib search (Phase 5): **not in mathlib** (no Chebotarev, no density, no prime-zeta layer; nearest is
  the unrelated single-prime cyclotomic decomposition-group lemma `galEquivZMod_stabilizer`).
- Composition check (Phase 6): **NOT-COMPOSABLE** (only the outer Galois reduction is mathlib; the
  zeta-comparison heart is new).

**Rationale:**

This is genuinely new, genuinely wanted mathematics: a clean statement of the fact that Frobenius elements
generate the Galois group, which is the algebraic heart of Chebotarev's density theorem and which mathlib
does not have in any form (the whole `Chebotarev` keyword is absent from the tree, as is the prime-ideal
density / Dedekind-zeta-residue machinery the proof rests on). So a NO bucket is wrong — neither
`NO-mathlib-has-it` (Phase 5: nothing there) nor `NO-composable-from-mathlib` (Phase 6: only the trivial
Galois wrapper composes; the degree-≤-1 zeta argument is irreducibly new). The result clears the "named
textbook theorem" bar and the composition gate.

It is **not** `YES-add-as-is`, however, because the Lean statement is a strict specialisation of the
literature-standard form along two mathematically real axes that the skill's gate forbids shipping narrow:
(a) it assumes `[IsMulCommutative Gal(L/K)]` (abelian), and (b) it tests only the chosen representative
`(frobeniusClass 𝔭).out` rather than the whole Frobenius conjugacy class. The project's own docstring
(lines 580–587) correctly explains these two are linked: the `.out`-only hypothesis *forces* the abelian
restriction, because for non-abelian `G` a non-normal `H` can contain one Frobenius representative per prime
without containing the class, and the split-completely transfer fails. The mathlib-canonical statement
quantifies over the class (or takes `H` normal), which simultaneously removes the abelian hypothesis — and
is what every cited source (Lenstra, Stevenhagen–Lenstra, Kedlaya, Stein) actually states. A third, cheaper
axis (the `m`-coprime restriction) is pure project plumbing: the `m = 1` corollary already at line 592 is
the all-unramified-primes form, so dropping `m` is mechanical.

**Reason for the generalisation:**
  - LITERATURE-WEAKENING: Phase 4b found the user's form strictly narrower than the literature-standard
    form (abelian + `.out` + coprime-subset vs. arbitrary Galois + whole class + all unramified primes).
  - MODERN-IDIOM: Phase 4c additionally flags dropping the `m`/coprime scaffolding (cheap) and quantifying
    over the conjugacy class (the same move that removes abelian-ness) as the contemporary, reusable
    formulation.

Proposed restatement (general, whole-class form — the mathlib target):

```lean
/-- **Frobenii generate the Galois group.** For a finite Galois extension `L/K` of number fields,
a subgroup `H ≤ Gal(L/K)` that meets the Frobenius conjugacy class of every nonzero prime of `K`
unramified in `L` is the whole group. -/
theorem subgroup_eq_top_of_forall_frobeniusClass_mem
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (H : Subgroup Gal(L/K))
    (hH : ∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsPrime → 𝔭 ≠ ⊥ → UnramifiedIn K L 𝔭 →
        ∀ σ : L ≃ₐ[K] L, ConjClasses.mk σ = frobeniusClass K L 𝔭 → σ ∈ H) :
    H = ⊤ := by
  sorry  -- general (non-abelian) proof; the current abelian `.out` proof is the H-normal special case
```

(The current `subgroup_eq_top_of_forall_frobenius_mem` abelian/`.out` theorem then becomes a corollary of
this, and the `_of_coprime` variant a further `m`-restricted corollary kept only if the κ-uniformity
caller still wants the coprime phrasing.)

Estimated cost of regeneralisation: **EXPENSIVE** (the whole-class/non-abelian direction needs genuine new
proof content; the abelian `.out` argument does not directly survive). EXPENSIVE does **not** downgrade the
verdict — per the skill, "too expensive, ship narrow" would itself be a BORDERLINE question, not a
self-resolving downgrade; here the right form is clearly identified, so the verdict stands and the cost is a
sequencing note.

Mathlib downstream this enables (MODERN-IDIOM):
  - A single canonical "Frobenii generate `Gal(L/K)`" lemma that *any* future Chebotarev / prime-density /
    Galois-representation development in mathlib would cite, with no abelian or coprime-`m` baggage.
  - It is the lemma mathlib's eventual Chebotarev-density formalisation must have; shipping the abelian
    `.out` form now would just have to be re-generalised later.
  - Composes directly with mathlib's existing `frobeniusClass`-analogue / `arithFrobAt` decomposition API
    and with the (project-contributed, eventually upstreamed) prime-ideal density layer.

Next action: run `/generalise Chebotarev.subgroup_eq_top_of_forall_frobenius_mem_of_coprime` (it will
tension against both the literature-standard whole-class form from Phase 3 and the drop-`m` modern-idiom
form from Phase 4c) **before** opening any PR. Realistically this is a larger effort: the general non-abelian
proof is its own development. The pragmatic upstreaming path is to first generalise the *coprime* axis away
(cheap, gives `subgroup_eq_top_of_forall_frobenius_mem`), then pursue the whole-class/non-abelian statement
as the actual mathlib contribution — and to ship it together with the project's prime-ideal density /
prime-zeta-asymptotics lemmas it depends on (those are themselves YES-track mathlib gaps), as one
coordinated `feat(NumberTheory): Chebotarev density` effort rather than this single lemma in isolation.

---

## Next step

Run `/generalise Chebotarev.subgroup_eq_top_of_forall_frobenius_mem_of_coprime` to produce the
whole-conjugacy-class, non-abelian, all-unramified-primes restatement (dropping the `m`-coprime scaffolding
along the way), tensioned against the Lenstra / Stevenhagen–Lenstra standard form. Do **not** open a mathlib
PR on the narrow abelian/`.out`/coprime form. Sequence the upstreaming together with the underlying
prime-ideal density / Dedekind-zeta-asymptotics lemmas (also absent from mathlib) as one coordinated
Chebotarev-density contribution.
