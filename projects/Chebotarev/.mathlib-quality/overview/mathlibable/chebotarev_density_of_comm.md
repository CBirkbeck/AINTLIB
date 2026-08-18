# /mathlibable report — `Chebotarev.chebotarev_density_of_comm`

> Step-9 single-declaration mathlibable assessment. Run from `/overview` follow-up.
> Environment note: local Lean build is stale, so `lake build` / `lean_local_search` /
> `lean_goal` were not run; the assessment reasons from the source statement (as instructed).
> Mathlib-index searches used Loogle's web endpoint + direct grep over the pinned mathlib
> checkout (`.lake/packages/mathlib`, rev `d90090f647ca`). ChatGPT-math MCP was down
> (Codex error); literature fallbacks (WebSearch + WebFetch + extracted source PDFs) were used.

---

### Baseline (Phase 0)
- lake build:               not run (build stale per task; reasoned from source) — decl elaborates per repo state on `main`
- decl `Chebotarev.chebotarev_density_of_comm`: ✓ resolved at `projects/Chebotarev/CebotarevDensity/Main.lean:103`
- true qualified name:      `Chebotarev.chebotarev_density_of_comm` (namespace `Chebotarev` opened at Main.lean:60; the parsed guess `Chebotarev.chebotarev_density_of_comm` is CORRECT)
- kind:                     theorem
- has sorry:                no
- module docstring summary: Chebotarev's density theorem for a finite Galois extension `L/K` of number fields, in conjugacy-class form, plus corollaries (Dirichlet AP, completely-split density).

---

### Statement (Phase 1)

`Chebotarev.chebotarev_density_of_comm` is **the abelian special case of Chebotarev's density
theorem**. For a finite *abelian* Galois extension `L/K` of number fields with Galois group
`G = Gal(L/K)`, and a conjugacy class `C ⊆ G`, it states that the Dirichlet density of the set of
primes `𝔭` of `𝓞 K` that are prime, unramified in `L`, and whose Frobenius conjugacy class equals
`C`, is `|C| / |G|`. Because `G` is abelian, every conjugacy class is a singleton, so `|C| = 1` and
the density is in fact `1/|G|` for each Frobenius element.

Variables / typeclasses (Lean side):
- `{K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]` — the number-field Galois extension (file-level `variable`s).
- `[FiniteDimensional K L]` — finiteness of the extension.
- `[IsMulCommutative Gal(L/K)]` — **the abelian hypothesis** (this is what distinguishes `_of_comm` from the general theorem).
- `(C : ConjClasses Gal(L/K))` — a conjugacy class of the Galois group.

Hypotheses: all carried as typeclass instances / the class `C`; no explicit prop hypotheses.

Conclusion (math): `δ({𝔭 prime, unramified, Frob-class = C}) = |C|/|G|` in the sense of Dirichlet density (which here `= 1/|G|`).

Conclusion (Lean):
```lean
HasDirichletDensity
  {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ frobeniusClass K L 𝔭 = C}
  ((Nat.card C.carrier : ℝ) / Nat.card Gal(L/K))
```

Proof body (2 lines):
```lean
obtain ⟨σ, rfl⟩ := ConjClasses.mk_surjective C
simpa [ConjClasses_carrier_card_eq_one_of_comm σ] using chebotarev_abelian K L σ
```
i.e. it pushes `C = mk σ`, uses the helper `ConjClasses_carrier_card_eq_one_of_comm` (singleton class ⇒ `|C|=1`),
and reads off `chebotarev_abelian K L σ` (density `(Nat.card Gal(L/K))⁻¹`).

Three bespoke project predicates appear in the statement (none are mathlib concepts):
- `HasDirichletDensity` (Density.lean:64) — `def`: the ratio `Σ_{𝔭∈S} N𝔭^{-s} / Σ_𝔭 N𝔭^{-s} → δ` as `s ↓ 1`.
- `frobeniusClass` (Frobenius.lean:188) — `def`: the Frobenius conjugacy class of a prime.
- `UnramifiedIn` (Frobenius.lean:62) — `def`: `𝔭 ≠ ⊥ ∧ ∀ maximal 𝔓 over 𝔭, Algebra.IsUnramifiedAt`.

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: a theorem named after a person (Chebotarev) and a main result of the project (listed under
`## Main results` / built on `chebotarev_abelian`). Literature width run EXHAUSTIVE regardless.

### One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure` → one-liner check **n/a**. (For the record the
proof body is 2 lines and is a pure specialization; that is the load-bearing fact for Phase 6, not
Phase 2b.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                 | Hit? | Standard form found | Notes |
|----|----------------------------------|-----------------------------------------------------------------------|------|---------------------|-------|
| 1  | WebSearch (specific form)        | "mathlib4 Chebotarev density theorem formalized"                      | partial | — | Confirms Chebotarev is a *target* of the PNT/FLT formalization effort; no claim it is in mathlib yet. |
| 2  | WebSearch (general/abelian form) | "Chebotarev density theorem abelian case Dirichlet density Frobenius conjugacy class" | yes | abelian ⇒ class size 1; `d(T_σ)=1/#H_σ`; generalizes Dirichlet AP | SL, MIT 18.785, Lenstra, Di Meglio notes. |
| 3  | WebSearch (named-after / aliases)| (covered by #1/#2; "Chebotarev / Chebotarëv / Frobenius density")     | yes | same | Frobenius's density theorem is the historical special case. |
| 4  | ChatGPT MCP                      | self-contained: is "abelian Chebotarev" named/standard; generality; logically prior or downstream of general thm | n/a | — | **MCP down** (Codex `exec` failed). Substituted by extracted primary-source PDFs (Lenstra, rows 9–10). |
| 5  | Local references                 | `ls refs/Chebotarev/`, `.mathlib-quality/references/`                 | n/a  | (absent) | No `refs/` store and no `references/` dir for this project on this checkout. |
| 6  | nLab                             | "Chebotarev density theorem"                                          | n/a  | — | Not a category-theoretic concept; nLab has only a stub. Recorded n/a. |
| 7  | nCatLab (if categorical)         | —                                                                     | n/a  | — | Not categorical. |
| 8  | Stacks Project (if alg geom)     | —                                                                     | n/a  | — | Analytic/arithmetic density statement, not in Stacks' scheme-theoretic scope. |
| 9  | Primary source: Lenstra, *The Chebotarev Density Theorem* (PDF, extracted) | full text | yes | "Frobenius symbol of p ... the conjugacy class {Frob_q : q\|p}. ... in the case of an abelian group, this set contains only a single [element]." | **Decisive for the abelian-case point.** Abelian case = singleton class. |
| 10 | Primary source: MIT 18.785 Lec 28; Stevenhagen–Lenstra Appendix (cited in module docstring) | full text / docstring | yes | density `#C/#G`; reduction to cyclic via `E = L^⟨σ⟩` | SL Appendix is the project's own cited proof of the general reduction. |
| 11 | recent arXiv (last 5 yrs)        | "Chebotarev density Lean formalization"                              | partial | — | Active formalization target (PNT+ / FLT projects); no separate mathlib decl. |

### Literature summary (Phase 3)

Concept identified as: **Chebotarev's density theorem — abelian (= Frobenius/Dirichlet) case**.
Sources agree on the standard form: **yes**. The *general* statement is "density of primes with
Frobenius class `C` is `#C/#G`"; the *abelian case* is the immediate specialization where each class
is a singleton, giving `1/#G` per Frobenius element, equivalently the (generalized) Dirichlet-density
form of Dirichlet's theorem on primes in arithmetic progressions.

Most general standard form: the **conjugacy-class statement for an arbitrary finite Galois extension**
(no commutativity assumption) — density `#C/#G`. The abelian case is **strictly weaker**.

Generality dimensions where the literature varies:
  - Galois group: cyclic ⊂ **abelian** ⊂ arbitrary finite. The abelian restriction is a *proper
    specialization* of the headline theorem.
  - Density notion: Dirichlet (analytic) density (used here) vs natural density (a strictly stronger,
    harder statement). The project uses Dirichlet density — the standard first form.
  - Field: number field (here) vs general global field. Number-field-only is the usual textbook scope.

Logical-priority finding (the key literature question for this decl): **the abelian case is
DOWNSTREAM of the general theorem, not an input to it.** Lenstra presents it as "if you apply this
theorem in the abelian case ... {p : p ≡ a mod m} has density 1/φ(m)" — i.e. a *corollary*. The
ingredient that bootstraps the general proof is the **cyclic** case (via the fixed field
`E = L^⟨σ⟩`), which in this project is `chebotarev_abelian` + `density_lift_through_fixedField`, NOT
`chebotarev_density_of_comm`. So `_of_comm` sits on the *output* side of the development.

Disagreement with the literature: none. The Lean statement faithfully encodes the standard
abelian-case statement (with Dirichlet density).

---

### Generality analysis — `Chebotarev.chebotarev_density_of_comm`

Literature-standard form (from Phase 3): the **general conjugacy-class** Chebotarev theorem, density
`#C/#G`, with **no `[IsMulCommutative]` hypothesis**.

| # | Parameter / hypothesis            | Current Lean form                | Literature-standard form        | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|----------------------------------|----------------------------------|---------------------|----------------------------------|
| 1 | `[IsMulCommutative Gal(L/K)]`     | abelian Galois group             | **arbitrary** finite Galois group | **YES**             | The general theorem holds without it — and is **already proved in this very file** as `chebotarev_density` (Main.lean:71), with identical conclusion. |
| 2 | `[FiniteDimensional K L]`         | finite extension                 | finite extension                 | no                  | Genuinely needed (counting/finite Galois group). |
| 3 | number field `K,L`               | number field                     | global field                     | yes (in principle)  | Function-field generality is a separate, larger project; the whole development is number-field-scoped. Out of scope for *this* decl. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (it carries an `[IsMulCommutative]`
hypothesis the headline theorem does not need).
Number of weakening opportunities found: 1 decisive (drop commutativity → general `chebotarev_density`).
Proposed restatement: **none needed** — the strictly-more-general form is literally
`Chebotarev.chebotarev_density` (Main.lean:71), which already exists, is sorry-free, and has the
*same* conclusion `HasDirichletDensity {…} (Nat.card C.carrier / Nat.card Gal(L/K))`.
Cost of restatement: **n/a / CHEAP** — there is nothing to re-prove; the general theorem is present.

> This is the crux: normally STRICTLY-NARROWER → `YES-but-generalise-first`. Here the generalisation
> target is **already a theorem in the same file**, so "generalise first" collapses to "delete the
> specialisation and use the general one" — which is a NO bucket (Phase 6), not a YES.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Downstream |
|----|----------|----------|------------------------|------------|
| 1  | "let X be a foo" → typeclass? | already done | `[IsMulCommutative …]`, `[IsGalois …]` are already typeclasses | — |
| 2  | sequences → filters? | no | `HasDirichletDensity` is already a `Tendsto … (𝓝[>] 1)` filter statement | clean already |
| 3  | construct → universal property? | no | it's a density equality, nothing to characterise universally | — |
| 4  | set+closure → bundled substructure? | no | — | — |
| 5  | vector-space/field → module/(semi)ring? | no | inherently arithmetic over `𝓞 K` | — |
| 6  | 1-categorical → higher? | no | — | — |
| 7  | concrete index → general structure? | **yes, but downward** | the "concrete index" here is the *abelianness* of `G`; the general-structure version is exactly `chebotarev_density` (drop `IsMulCommutative`) | the general theorem already realises this |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no new one** — the statement is already in idiomatic mathlib form (typeclasses,
filter-based density). The only "generalisation" is removing the commutativity hypothesis, and that exact
general statement is `chebotarev_density`, already present. So there is no separate modern-idiom restatement
to ship; the idiomatic, maximally-general object is the *other* theorem in the file.

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (no definitional equalities or instances introduced).

---

### Mathlib search-status: `Chebotarev.chebotarev_density_of_comm`

[A] Lean-Finder       "Chebotarev density Frobenius conjugacy class"     no hits (concept absent from mathlib)
[B] Loogle            web endpoint `q=Chebotarev`                         **error: unknown identifier 'Chebotarev'** ⇒ no such name in mathlib index
[C] LeanSearch        "Dirichlet density of prime ideals" / "Chebotarev" endpoint 404/405 (service path moved); corroborated by D
[D] Grep mathlib src  rev `d90090f647ca`, `.lake/packages/mathlib/Mathlib`:
                        • `chebotarev|cebotarev|tchebotarev`              → **0 hits**
                        • `DirichletDensity|dirichlet_density|density of primes|analytic density` → **0 hits** (no Dirichlet-density-of-primes framework anywhere in mathlib)
                        • `frobeniusClass|FrobeniusClass`                 → **0 hits**
                        Present (building blocks only):
                        • `AlgHom.IsArithFrobAt` / `IsArithFrobAt` + `IsArithFrobAt.exists_of_isInvariant`, `.conj` — RingTheory/Frobenius.lean (the Frobenius *element*, used by this project)
                        • `Nat.infinite_setOf_prime_and_eq_mod` — LSeries/PrimesInAP.lean (Dirichlet AP, **infinitude only — not a density statement**)
                        • `ConjClasses.card_carrier` — GroupTheory/GroupAction/Quotient.lean:417 (relevant to the helper, not the main thm)
[E] Name pattern      (stale build; lean_local_search unavailable) — n/a: covered by grep over mathlib source

Searched for both:
  - the user's form (abelian Chebotarev, Dirichlet density) — absent.
  - the literature-standard general form (conjugacy-class `#C/#G`, Dirichlet density) — absent.

Concluded: **not in mathlib** (all available methods exhausted, both forms). Mathlib has the
Frobenius-element machinery and the *infinitude* form of Dirichlet's theorem, but **no Dirichlet-density
framework and no Chebotarev statement of any kind.** ⇒ the genuinely-mathlibable object in this file is
the *general* `chebotarev_density` (and the density `def`s), NOT this abelian specialization.

---

### Call sites — `Chebotarev.chebotarev_density_of_comm`

Internal use count: **0** (within the project, excluding the declaring line).
External-to-file callers: **0 files**.
Whole-repo grep (`grep -rn chebotarev_density_of_comm` over all of AINTLIB): the name appears **only**
at its own declaration `Main.lean:103`. Nothing consumes it — not `infinite_setOf_frobenius_class`,
not `density_split_completely`, not `dirichlet_primes_in_AP` (those all go through the *general*
`chebotarev_density`).

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none)           | — |

Inline-derivation grep: the *general* theorem `chebotarev_density` is the one actually used downstream;
`_of_comm` is a dead-end specialization (K = 0, no inline re-derivation of its specific abelian form
elsewhere because the general form already covers every call).

> Composability signal (per mathlibable-verdicts.md): **K = 0 internal uses** for a result that is a
> ≤1-line specialization of an already-present more-general theorem ⇒ strong NO-composable signal.

### Composition check (Phase 6)

Can `chebotarev_density_of_comm` be derived from already-available results in ≤3 chained calls?

Attempt 1 — from the project's own general theorem (same file):
```lean
example [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (C : ConjClasses Gal(L/K)) :
    HasDirichletDensity {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ frobeniusClass K L 𝔭 = C}
      ((Nat.card C.carrier : ℝ) / Nat.card Gal(L/K)) :=
  chebotarev_density C            -- 1 call; the [IsMulCommutative] instance is simply ignored
```
  - Decls used: `Chebotarev.chebotarev_density` (Main.lean:71).
  - Result: **succeeds.** `chebotarev_density` has the *identical* conclusion and a *strict subset*
    of the hypotheses (it lacks `[IsMulCommutative]`), so the abelian statement is a 0-step
    specialization — literally the general theorem with one extra unused instance in scope.

Conclusion: **COMPOSABLE** (in fact a pure specialization, 1 call, of a theorem already in the file).

### Composition heuristics check
`chebotarev_density C` is a single function application with no rewriting/automation glue → a genuine
composition, not a proof in disguise (top row of the heuristics table: "one function call → yes").

---

## Verdict: `Chebotarev.chebotarev_density_of_comm`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): abelian Chebotarev is a standard but **strictly weaker, downstream**
  corollary of the general conjugacy-class theorem (Lenstra: abelian ⇒ singleton class; "apply this
  theorem in the abelian case" → density `1/φ(m)`). It is not a logically-prior lemma.
- Generality (Phase 4): **STRICTLY NARROWER THAN STANDARD** — carries `[IsMulCommutative]`; the general
  form (no commutativity) is the literature standard.
- Mathlib search (Phase 5): **not in mathlib** in any form; mathlib has only Frobenius-element building
  blocks and the *infinitude* (non-density) form of Dirichlet AP. The mathlibable object here is the
  *general* `chebotarev_density`, not this specialization.
- Composition (Phase 6): **COMPOSABLE** — `chebotarev_density C` proves it in one call (the abelian
  hypothesis is ignored). Call sites: **K = 0**.

**Rationale:**

`chebotarev_density_of_comm` is the abelian specialization of a theorem the project **already proves in
the same file** — `chebotarev_density` (Main.lean:71) — which has the identical conclusion and *fewer*
hypotheses (no `[IsMulCommutative]`). The abelian statement therefore follows in a single call
(`chebotarev_density C`, with the commutativity instance merely present-but-unused), is used **nowhere**
in the repository (K = 0 call sites), and adds no mathematical content over the general theorem. Per the
skill's iron rule (Bourbaki 2.0: add the most general form, no wrapper lemmas), the upstreaming target is
the *general* `chebotarev_density` together with the project's `HasDirichletDensity` / `frobeniusClass`
density framework — not this corollary. Shipping `_of_comm` to mathlib would be shipping a thin
specialization of a stronger result, which mathlib declines on principle.

Note this is NOT `NO-mathlib-has-it`: mathlib has neither form (Phase 5 found no Dirichlet-density or
Chebotarev machinery at all). The "composable" building block is the project's own general theorem, which
is the genuine mathlib candidate. So the correct action is local refactor (drop the specialization), and
the mathlibable energy should be redirected to `chebotarev_density` + the density framework.

**WHY not (refactor-actionable):**
Mathlib does not have this, but the project does have the strictly-more-general `chebotarev_density`,
from which `_of_comm` is a one-call specialization. No new lemma (local or mathlib) is justified for the
abelian case as a *separate* result.

  Building block (already in the project):  `Chebotarev.chebotarev_density`  (Main.lean:71)
  Composition (≤1 line):
  ```lean
  -- wherever the abelian-case density is needed, with [IsMulCommutative Gal(L/K)] in scope:
  example [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (C : ConjClasses Gal(L/K)) :
      HasDirichletDensity {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ frobeniusClass K L 𝔭 = C}
        ((Nat.card C.carrier : ℝ) / Nat.card Gal(L/K)) :=
    chebotarev_density C
  ```
  Call sites in the project: **K = 0** — so the refactor is *just a deletion*; there are no consumers
  to update.
  Next action: **delete `chebotarev_density_of_comm`** (and, if it becomes unused, its helper
  `ConjClasses_carrier_card_eq_one_of_comm`) from `Main.lean`. The abelian case needs no standalone
  declaration; any future consumer calls `chebotarev_density` directly (the `IsMulCommutative` instance
  is simply available in scope and ignored). Redirect mathlibable effort to `chebotarev_density` and the
  `HasDirichletDensity` / `frobeniusClass` / `UnramifiedIn` framework.

> CAVEAT / project-policy note (not a verdict change): AINTLIB is WIP and the docstring advertises
> `_of_comm` as a stated "abelian case". If the project deliberately wants the abelian case as a named,
> citable entry point (pedagogy / blueprint cross-link), that is a *local* keep-decision and does not
> bear on mathlib: as a mathlib contribution it is still subsumed by `chebotarev_density`. The
> `NO-composable` verdict is about mathlib inclusion, and is firm.

---

## Next step

Delete `chebotarev_density_of_comm` (a zero-use, one-call specialization of the file's own
`chebotarev_density`); there are no call sites to update. For mathlib, pursue the **general**
`Chebotarev.chebotarev_density` plus the project's Dirichlet-density framework — neither exists in
mathlib (rev `d90090f647ca`), and they are the genuinely-novel, maximally-general objects.
