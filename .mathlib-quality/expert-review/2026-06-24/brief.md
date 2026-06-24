# Review brief #3 — Status check: formalising Wedhorn Theorem 8.28(b) (the structure presheaf on `Spa(A,A⁺)` is a sheaf)

*Prepared 2026-06-24 for a reviewer fluent in adic spaces and Huber's theory (Wedhorn's
*Adic Spaces*; Huber's papers). Self-contained: no access to the formalisation is needed.
We use Wedhorn's notation throughout. This is a whole-project status check; it supersedes
review #2 (the inducing step) and folds in its questions.*

---

## 1. Goal

We are formalising, in a dependently-typed proof assistant on top of a large mathematics
library, **Wedhorn's Theorem 8.28(b)**: *if `A = (A, A⁺)` is a complete affinoid ring whose
underlying ring is a strongly noetherian Tate ring, then the structure presheaf `𝒪_X` on the
adic spectrum `X = Spa(A, A⁺)` is a sheaf* (of complete topological rings, on the basis of
rational subsets). This brief is a **status check**: what is rigorously done, what is in
progress, what remains — and a request that the reviewer **(a) check that our key statements
are not vacuous, trivially satisfiable, or otherwise "junk" (that the hypotheses we carry are
faithful to Wedhorn and do not secretly trivialise the conclusions), and (b) sanity-check the
plan for the remaining work.**

---

## 2. Background and references

### 2.1 Setting and conventions

- `A` is a Huber ring (Wedhorn: *f-adic ring*): a topological ring with an open subring `A₀`
  (a *ring of definition*) carrying the `I`-adic topology for a finitely generated *ideal of
  definition* `I ⊆ A₀`.
- `A` is **Tate** if it has a topologically nilpotent unit `ϖ`.
- `A°` is the subring of **power-bounded** elements; `A°°` the (topologically nilpotent)
  ideal; a **ring of integral elements** `A⁺` is an open, integrally closed subring with
  `A°° ⊆ A⁺ ⊆ A°` (Wedhorn Def 7.14). An **affinoid ring** is a pair `(A, A⁺)`.
- `Spa(A, A⁺) = { v ∈ Cont(A) : v(f) ≤ 1 for all f ∈ A⁺ }`, `Cont(A)` the continuous
  valuations (Wedhorn Def 7.23).
- For a rational datum `(T, s)` (`T` finite, `T·A` open) the **rational subset** is
  `R(T/s) = { v ∈ Spa A : v(t) ≤ v(s) ≠ 0, ∀ t ∈ T }`; the presheaf value is the complete
  Tate ring `𝒪_X(R(T/s)) = A⟨T/s⟩` (adjoin `t/s`, complete), with `𝒪_X(R(T/s))⁺` its ring of
  integral elements (Wedhorn 7.19, 8.2, 8.16). In the formalisation `𝒪_X(R(T/s))` is the
  completion of the localisation `A_s` with the `I·A_s`-adic ("localisation") topology; the
  presheaf is indexed by rational data, not abstract opens.
- We write `B = 𝒪_X(D)` for the value on a rational locale `D`, `B⁺ = 𝒪_X(D)⁺`.

### 2.2 References

- **[W]** T. Wedhorn, *Adic Spaces* (lecture notes; all section/number references are to this
  text). Items used: Def 7.14 (ring of integral elements); Prop 7.19 + Lemma 7.20 (`A⟨T/s⟩⁺`
  is a ring of integral elements); Lemma 7.45, Prop 7.49/7.51(2)/7.52(2) (analytic Spa-points,
  Nullstellensatz); Prop 7.41 (height one); Lemma 7.47(4) (completion correspondence); Prop
  6.17/6.18 (closedness of ideals / Banach OMT); Cor 8.32 (`∏ 𝒪_X(Dᵢ)` faithfully flat); Prop
  8.30 (restriction flat); Lemma 8.31; Remark 7.55 (geometric flatness chain); Example
  6.38–6.39 (`𝒪_X(D)` strongly noetherian); Lemma 8.34 + Prop A.3/A.4 (Čech / sheaf
  criterion); Thm 8.28(b) (headline).
- **[Hu1]** R. Huber, *Continuous valuations*, Math. Z. 212 (1993) — `Cont(A)`, height-one;
  [Hu1] 2.4.3 = completion-transfer of integral closedness.
- **[Hu2]** R. Huber, *Continuous valuations* (companion) — Lemma 3.3 (`= [W] 7.18`, the
  `σ/τ` bijection of continuous valuations under completion); used for the power-bounded lift.
- **[Hu3]** R. Huber, *A generalization of formal schemes and rigid analytic varieties*,
  Math. Z. 217 (1994) — [Hu3] 2.6 `= [W] 7.54`.

### 2.3 State of the art

Theorem 8.28(b) is classical (Huber; Wedhorn's notes are an exposition) and, to our knowledge,
**not previously formalised**. The deep inputs are exactly those Wedhorn cites to Huber: a
Banach open-mapping theorem in the non-archimedean, non-σ-compact setting (6.16/6.18); the
Nullstellensatz-type existence of analytic Spa-points (7.45/7.49/7.51); and completion-
stability of `Cont` / integral-closedness (7.18/7.47). Our decomposition deliberately bottoms
out at *these* statements rather than inventing easier substitutes (see §8.4 for why).

---

## 3. Strategy

Wedhorn reduces the sheaf property on the rational basis (Prop A.3/A.4) to two statements
about every finite rational cover `(Dᵢ)` of a rational locale `D₀`:

1. **Embedding** `𝒪_X(D₀) → ∏ᵢ 𝒪_X(Dᵢ)` is a topological embedding = (a) **injective** +
   (b) **inducing** (right subspace topology).
2. **Gluing / exactness** of the Čech complex: a compatible family glues uniquely.

Our plan mirrors this:

- **Injective** ← `∏ᵢ 𝒪_X(Dᵢ)` faithfully flat over `𝒪_X(D₀)` (Cor 8.32) ← each restriction
  flat (Prop 8.30) ← the dominating-unit Laurent chain (Remark 7.55) of per-step flat maps,
  base case Example 6.38 (`𝒪_X(D)` strongly noetherian) + Lemma 8.31.
- **Inducing** ← image = equaliser of the double-product maps (surjectivity onto the equaliser
  uses gluing), closed range, and the **Banach OMT** 6.16 (σ-compact-free): a continuous
  injective `A`-linear map with closed range over a ring with a topologically nilpotent unit
  is an embedding.
- **Gluing** ← `𝒪_X`-acyclicity of rational covers (Lemma 8.34 + abstract Čech Prop A.3),
  reduced to Laurent covers and the Tate acyclicity of Lemma 7.54.

**Self-imposed constraint (please police):** the headline must not acquire extra hypotheses.
Restriction maps being well-defined needs `s` invertible and `t/s` power-bounded in `𝒪_X(D')`;
Wedhorn *proves* these (7.52(2), 7.41), so we **derive** them inside the proof (the "LL
package"), rather than assuming them on the headline.

---

## 4. Definitions to sanity-check

**Definition 4.1 (ring of integral elements — our interface).** For a subring `B ⊆ A`, "`B`
is a ring of integral elements" packages Wedhorn Def 7.14: `B` open, integrally closed in `A`,
`B ⊆ A°`. This is our *faithful affinoid interface*. The base bundle "`(A,A⁺)` is affinoid"
additionally records `A⁺ ⊆ A₀(D)` for each rational locale `D`; it implies Def 4.1 for `A⁺`.

> *Reviewer check:* is Def 4.1 the right axiomatisation, and does carrying it (for `A⁺`, and —
> §5.6 — for the completions `𝒪_X(D)⁺`) ever risk vacuity, i.e. is there a reading under which
> it is unsatisfiable or trivialises a conclusion?

**Definition 4.2 (`𝒪_X(D)⁺ = Ĉ`).** `𝒪_X(D)⁺` is the **integral closure, inside the completion
`𝒪_X(D)`, of `Ĉ₀`**, where `Ĉ₀` is the closure of the image of `C = (A⁺[T/s])^{int}` (integral
closure of `A⁺[T/s]` in `A_s`). This is Wedhorn 8.16's `Ĉ`. *Design point:* defining `B⁺` as
the integral closure **in the completion** makes "integrally closed" hold by construction
(idempotence), avoiding [Hu1] 2.4.3 (integral-closedness commutes with completion). We then
separately need `Ĉ₀` **open** (done) and **power-bounded** (§8.1).

**Definition 4.3 (rational cover; the sheaf condition).** A finite family `(Dᵢ)` covers `D₀`
when the `R(Dᵢ)` cover `R(D₀)` (Def 7.29). `IsSheafy A` is the conjunction over all such
covers of (embedding, gluing) — Prop A.4's repackaging of the sheaf property on the basis.

> *Reviewer check:* is `IsSheafy A` (embedding + gluing over Def-7.29 covers) the correct
> rendering of "`𝒪_X` is a sheaf", or weaker?

---

## 5. Established results (machine-checked, sorry-free unless stated; "axiom-clean" = no
appeal to any unproven statement)

**Theorem 5.1 (headline, assembled — conditional on §6/§8 leaves).** For `A` complete strongly
noetherian Tate with compatible `A⁺`, `IsSheafy A` holds as (embedding, gluing). *We verified
its elaborated hypotheses are exactly Wedhorn 8.28(b)* — the interface work of §5.6 leaked no
hidden binder onto it. The reduction to the §6/§8 leaves is complete; it is not yet
axiom-clean (depends on those leaves).

**Theorem 5.2 (`Spa(𝒪_X(D)) ≅ R(D)`, Spa-point pullback).** Axiom-clean. Used pervasively.

**Theorem 5.3 (LL-unit; 7.52(2)/7.49).** For `R(D') ⊆ R(D)`, `s_D` is a unit in `𝒪_X(D')`.
Axiom-clean. *Sketch:* every Spa-point of `𝒪_X(D')` pulls back into `R(D') ⊆ R(D)`, where
`s_D` does not vanish; the pair-free complete-affinoid unit criterion (7.45 containment) gives
invertibility.

**Theorem 5.4 (`𝒪_X(D)` strongly noetherian; Example 6.38–6.39).** `𝒪_X(D)` is topologically
of finite type over the strongly noetherian Tate ring `A`, hence strongly noetherian; the
comparison `𝒪_X(D) ≅ A⟨X⟩/ker` is established for general `D`. Axiom-clean. (The general-`n`
multivariate Tate topology and "every ideal is closed" Prop 6.17 are also axiom-clean.)

**Theorem 5.5 (per-step flatness; Prop 8.30 basic Laurent step).** Each basic Laurent
refinement step is flat. Axiom-clean. The whole-space dominating-unit chain (Remark 7.55)
assembling these is built.

**Theorem 5.6 (ring-of-integral-elements interface for completions — recent frontier).**
`𝒪_X(D)⁺` (Def 4.2) is a ring of integral elements, *provided `A⁺` is one*. Of its axioms:
  - **integrally closed: axiom-clean and free** (Def 4.2 design);
  - **open: axiom-clean (proven this session).** Faithful to Prop 7.19 + Lemma 7.20: `A⁺` open
    ⟹ `A⁺⟨X⟩` open ⟹ `(A⁺⟨X⟩)^{int}` open. Concretely, the first `I`-adic neighbourhood of `0`
    in the completion lands in `Ĉ₀` via the **absorption `A₀·I ⊆ I ⊆ A⁺`** (`I` is an ideal of
    `A₀`; `I ⊆ A°° ⊆ A⁺`); `Ĉ₀` is closed and contains a neighbourhood of `0`, hence open. The
    absorption is packaged by: every monomial in the `A₀[T/s]` generators factors as
    `(image of a₀)·p` with `a₀ ∈ A₀`, `p` in the `A⁺`-subring, after which one multiplication
    by an `I`-element is absorbed into `A⁺`.
  - **power-bounded (`⊆ A°`): open**, and the statement currently in the code is over-strong
    (§8.1).
The interface is threaded through the whole downstream chain; the headline supplies it from
its affinoid hypothesis and — verified — adds no hypothesis to `IsSheafy`.

**Theorem 5.7 (Banach OMT, σ-compact-free; 6.16).** Over a ring with a topologically nilpotent
unit, a continuous bijective module map is open; hence a continuous injective linear map with
closed range is an embedding. Built (replacing an earlier `[σ-compact]` version unfulfillable
for `Aⁿ`).

**Theorem 5.8 (Cor 8.32 maximals criterion).** Faithful flatness of `∏ᵢ 𝒪_X(Dᵢ)` reduces to
per-step flatness (5.5) + "every maximal ideal of `𝒪_X(D₀)` survives in some `𝒪_X(Dᵢ)`", the
latter from analytic Spa-point existence (7.45/7.49). The faithful route (an earlier
prime-surjection rendering was deleted).

**Theorem 5.9 (Čech engine; Prop A.3, Lemma 7.54).** The abstract two-term Čech machinery and
the Laurent-cover reduction are axiom-clean; Wedhorn 7.54 (`=[Hu3] 2.6`) and the whole-space
Lemma 8.34 + A.3 chain are complete.

---

## 6. In progress (statements fixed; proofs rest on a small leaf set)

**Leaf A — injectivity via faithful flatness.** Reduces to Cor 8.32 (5.8) → Prop 8.30 (5.5) →
the **LL package** `HasLocLiftPowerBounded` (derived, not assumed). LL = LL-unit (5.3, done) +
**LL-bdd** (`t/s` power-bounded in `𝒪_X(D')`). LL-bdd reduces to (i) a continuity input
(reverse of 7.10 / Huber 3.1) — **discharged this session**; (ii) a power-bounded lift citing
**[Hu2] 3.3** (`=[W] 7.18`), plus the interface of §5.6. So Leaf A is built modulo the §8.1
boundedness residual and the [Hu2] 3.3 cite.

**Leaf B — inducedness.** Built from: image = equaliser (surjectivity uses Leaf C), closed
range, Banach OMT (5.7). Rests on Leaf C and any residual in the OMT chain (we believe the OMT
is complete; please confirm).

**Leaf C — gluing.** One line from the rational-cover `𝒪_X`-acyclicity result (Theorem 5.9
engine). The whole-space acyclicity is complete; the gap is **transport to general bases**
("R2 transport":
instantiate the absolute result at `B = 𝒪_X(U)` and transport along `Spa(B) ≅ U`).

---

## 7. Ticket board

| Item | Mathematical content | Status |
|---|---|---|
| `Spa(𝒪(D)) ≅ R(D)` | rational-subset ↔ value-ring spectrum | **done** (axiom-clean) |
| LL-unit | `s` unit in `𝒪_X(D')` (7.52(2)) | **done** (axiom-clean) |
| `𝒪_X(D)` strongly noetherian | Example 6.38 | **done** (axiom-clean) |
| per-step flat | Prop 8.30 basic step | **done** (axiom-clean) |
| Remark 7.55 chain | dominating-unit fold ⇒ Prop 8.30 | **built** |
| interface: integrally closed | `𝒪_X(D)⁺` integrally closed | **done, free** |
| interface: open | `𝒪_X(D)⁺` open (7.19/7.20) | **done this session** (axiom-clean) |
| interface: power-bounded | `𝒪_X(D)⁺ ⊆ 𝒪_X(D)°` (7.19/7.20) | **open** — §8.1 |
| LL-bdd | `t/s` power-bounded (7.41/7.18) | **built modulo [Hu2] 3.3** |
| Cor 8.32 faithfully flat | injectivity keystone | **built** (on LL + maximals) |
| Banach OMT 6.16 | inducedness keystone | **built** |
| Leaf C R2-transport | acyclicity on general bases | **open** |
| headline 8.28(b) | `IsSheafy A` | **assembled**; depends on the above |

---

## 8. Where we are stuck (please scrutinise these most)

**8.1 The boundedness residual `𝒪_X(D)⁺ ⊆ 𝒪_X(D)°` — probable statement error.** Our code
states this as **`Ĉ₀` is uniformly (von Neumann) bounded**, then derives "power-bounded" from
"integral over a bounded subring" (5.30(4)). We now believe uniform boundedness is **strictly
stronger than Wedhorn's 7.19/7.20**, which prove only `A⟨T/s⟩⁺ ⊆ A⟨T/s⟩°` (power-bounded):
`A⁺⟨X⟩ ⊆ A°⟨X⟩ ⊆ A⟨T/s⟩°` (Lemma 7.20), then integral closure preserves `⊆ A°`. A ring of
integral elements need **not** be uniformly bounded (in a non-uniform Tate ring `A°` is
unbounded). The uniform statement holds for the *ring of definition* `A₀[T/s]` only because
rings of definition are bounded; `(A⁺[T/s])^{int} ⊄ A₀[T/s]`, so that route does not transfer.

*Intended fix:* restate as the **power-bounded containment** `Ĉ₀ ⊆ 𝒪_X(D)°` and conclude the
interface axiom via "`A°` integrally closed". Faithful to 7.20 but needs three standard facts
not yet formalised: (i) `A⁺[T/s] ⊆ (A_s)°` (`A⁺ ⊆ A°` maps to power-bounded; `t/s` power-
bounded in `A_s`); (ii) `(A_s)°` and `𝒪_X(D)°` **integrally closed** (we have the "integral
over *bounded*" form, not the "integral over `A°`" form); (iii) closure of power-bounded ⊆
power-bounded.

> **Q1.** Is uniform boundedness of `𝒪_X(D)⁺` actually false in general (we believe so), and is
> the power-bounded reroute via "`A°` integrally closed" the cleanest faithful path — or is
> `𝒪_X(D)⁺` genuinely bounded for the *complete strongly noetherian* `A` of 8.28(b)
> specifically (e.g. via uniformity of such rings)?

**8.2 Deep external leaves (cited to Huber).**
- **[Hu2] 3.3 (`=[W] 7.18`)** — the power-bounded lift for LL-bdd (completion preserves the
  bound via the `σ/τ` correspondence). Treated as a cited external leaf.
- **Prop 6.17/6.18** (closedness of f.g. ideals / Banach OMT context) — Wedhorn marks the
  proof "missing"; we lean on the σ-compact-free 6.16 we proved.

> **Q2.** Are we right to treat [Hu2] 3.3 and 6.17/6.18 as legitimate cited leaves (faithful
> to Wedhorn's own deferral), and is our σ-compact-free 6.16 adequate for the role 6.18 plays
> in inducedness?

**8.3 Leaf C relativisation (R2-transport).** Čech acyclicity is proven for whole-space
covers; transporting to a cover of a rational subset `U` uses `Spa(𝒪_X(U)) ≅ U` (Prop 8.2,
Remark 8.4, Prop 8.16) to re-instantiate the absolute result with base `B = 𝒪_X(U)` (again
complete strongly noetherian Tate, `B⁺ = 𝒪_X(U)⁺`). We chose *not* to build a bespoke relative
Čech theory.

> **Q3.** Is "instantiate the absolute acyclicity at `B = 𝒪_X(U)`, transport along
> `Spa(B) ≅ U`" the correct and complete reduction, or does relativisation hide a subtlety
> (e.g. compatibility of `B⁺` with the integral structure induced on the subset)?

**8.4 Vacuity / faithfulness audit (the core request).** This project has a documented history
of *unfaithful* decompositions that were sorry-free but wrong: (i) carrying `[A₀ noetherian]`
(ring-of-definition noetherian) on case-(b) statements — **false for `ℂ_p`** and not what
8.28(b) needs; (ii) `[A` has a basis of open ideals`]` on a Tate chain — **vacuous**, since a
Tate ring has a topologically nilpotent unit and hence no proper open ideal, so the hypothesis
is unsatisfiable and empties every lemma under it; (iii) "orphan" leaves with no Wedhorn
counterpart that turned out false (e.g. "noetherian ⇒ strongly noetherian"). We now run a
"`ℂ_p` test" on every topological/finiteness hypothesis.

> **Q4 (core).** Please scrutinise our *current* live hypotheses for the same failure modes:
> - the **affinoid-ring interface** on the headline and threaded to the completions (`A⁺` and
>   `𝒪_X(D)⁺` are rings of integral elements, Def 4.1/4.2): faithful and non-vacuous, or does
>   it smuggle in strength / could it be unsatisfiable for the rings we target?
> - the headline's **`complete strongly noetherian Tate`** bundle: exactly 8.28(b), or
>   over-/under-constrained?
> - **`HasLocLiftPowerBounded` derived rather than assumed**: is deriving "`s` a unit, `t/s`
>   power-bounded" inside the proof correct, and does the derivation actually use the
>   hypotheses (not circularly assume the conclusion)?
> - the leaf **routes** — inducedness via *equaliser + OMT*; injectivity via *Cor 8.32
>   faithful flatness / maximals*; gluing via *Čech acyclicity*: do these mirror Wedhorn, or
>   have we substituted a convenient-but-different argument anywhere?

---

## 9. Consolidated questions

- **Q1 (statement).** Uniform boundedness of `𝒪_X(D)⁺`: false in general + power-bounded
  reroute correct? Or genuinely bounded for complete strongly noetherian Tate `A`?
- **Q2 (external leaves).** [Hu2] 3.3 and 6.17/6.18 legitimate as cited leaves; σ-compact-free
  6.16 adequate?
- **Q3 (relativisation).** Is the R2-transport reduction of Čech acyclicity complete?
- **Q4 (faithfulness/vacuity).** Affinoid interface, headline bundle, derived LL package, and
  leaf routes — all faithful and free of vacuity/over-hypothesis?
- **Q5 (plan).** Is the work-order sensible: (a) fix §8.1 boundedness, (b) close LL-bdd modulo
  [Hu2] 3.3, (c) finish Leaf C R2-transport, (d) confirm Leaf B OMT residual, (e) collapse the
  headline to axiom-clean? Anything mis-prioritised or missing?

---

## 10. Document metadata

- Project: formalisation of Wedhorn *Adic Spaces* Thm 8.28(b) (`𝒪_X` is a sheaf on `Spa A`).
- Generated: 2026-06-24. Supersedes review #2 (2026-06-19, the inducing step).
- Build status: compiles cleanly. Headline assembled; reduces to the §6/§8 leaves. One
  frontier sub-result (`𝒪_X(D)⁺` openness) proven sorry-free this session; one (`𝒪_X(D)⁺`
  boundedness) flagged as a probable statement error (§8.1).
- Recent activity: ring-of-integral-elements interface refactor (integral-closedness made
  free; interface threaded with the headline's stated hypotheses verified unchanged); openness
  leaf closed; boundedness divergence documented.
- Caveat: much of the repository belongs to *adjacent* developments (perfectoid/tilting,
  Fargues–Fontaine, foundational valuation theory) **not** on the 8.28(b) critical path; this
  brief concerns only the 8.28(b) leaves above.
