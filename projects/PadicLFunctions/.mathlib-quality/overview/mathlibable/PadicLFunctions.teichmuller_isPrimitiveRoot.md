# /mathlibable report — `PadicLFunctions.teichmuller_isPrimitiveRoot`

**Final verdict: `YES-but-generalise-first`** — the underlying mathematical
content (the Teichmüller lift `ω(u)` of a unit whose reduction generates
`(ZMod p)ˣ` is a **primitive `(p−1)`-th root of unity** in `ℤ_[p]`; equivalently
`ℤ_[p]` contains a primitive `(p−1)`-th root and `HasEnoughRootsOfUnity ℤ_[p]
(p−1)`) is canonical p-adic number theory that mathlib **does not have for
`ℤ_[p]`** (it only has `HasEnoughRootsOfUnity (ZMod p) (p−1)` for the *residue
field*). But the declaration as written is **not** the form to ship: (1) its
hypothesis is the full infinite tower `∀ n, zpowers(unitsToZModPow p n u) = ⊤`
when the proof uses **only the `n = 1` level**, and is phrased over the
project-specific reduction map `PadicMeasure.unitsToZModPow`; the literature- and
mathlib-idiomatic form takes a plain generator of `(ZMod p)ˣ`. (2) It is built on
a **project-local** `PadicInt.teichmuller : ℤ_[p]ˣ →* ℤ_[p]ˣ`, not mathlib's
`Perfection.teichmuller₀`. (3) **A cleaner sibling already exists** in this same
repo — `FltRegularBernoulli.teichmuller_isPrimitiveRoot_of_generator`
(`Characters.lean:188`) — stated exactly over a generator hypothesis and feeding
a `HasEnoughRootsOfUnity ℤ_[p] (p−1)` instance. The mathlib target is the
*deduplicated, generator-hypothesis* statement (ideally packaged as the
`HasEnoughRootsOfUnity ℤ_[p] (p−1)` instance), not this `unitsToZModPow`-tower
wrapper.

---

### Baseline (Phase 0)
- lake build:               **not re-run** (stale/slow per task note) — **reasoned from source** ("build not re-run; reasoned from source").
- decl `PadicLFunctions.teichmuller_isPrimitiveRoot`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ResidueZeta.lean:126`.
- kind:                      `theorem`.
- has sorry:                 no (the proof and every dependency — `PadicInt.teichmuller`, `teichmullerFun_pow_card_sub_one`, `teichmullerFun_sub_self_mem`, `PadicMeasure.unitsToZModPow` — are `sorry`-free).
- module docstring summary:  "The residue of ζ_p at s = 1 (RJW §7)". This theorem (tagged R7.2a) is a *supporting lemma* feeding the branch-denominator non-vanishing `branch_denom_ne_zero` (RJW Lemma 7.2(i)), not the file's headline residue/pole result.

(Phase 4.5 — diamond/defeq risk — is `n/a`: the declaration is a `theorem`, not a `def`/`class`/`instance`, so it introduces no definitional equalities or typeclass-search paths.)

---

### Statement (Phase 1)

`PadicLFunctions.teichmuller_isPrimitiveRoot` is **a theorem**. Let `p` be a
prime (`[Fact p.Prime]`) and let `u : ℤ_[p]ˣ` be a p-adic unit such that, **for
every `n`**, the reduction `unitsToZModPow p n u ∈ (ZMod (pⁿ))ˣ` is a generator
(its `zpowers` are `⊤`). Then the **Teichmüller value** `ω(u) =
PadicInt.teichmuller p u ∈ ℤ_[p]ˣ` is a **primitive `(p−1)`-th root of unity**:

  `IsPrimitiveRoot (PadicInt.teichmuller p u) (p − 1)`.

Mathematically: `ω(u)` is the unique `(p−1)`-th root of unity in `ℤ_[p]`
congruent to `u` mod `p`; since `u mod p` generates `(ZMod p)ˣ` (order `p−1`) and
ω is a section of reduction, `ω(u)` has exact multiplicative order `p−1`, i.e. it
is a primitive `(p−1)`-th root.

Variables / typeclasses (Lean side):
- `p : ℕ` with `[hp : Fact p.Prime]`.
- `u : ℤ_[p]ˣ` (implicit) — a p-adic unit.

Hypothesis (Lean side):
- `hgen : ∀ n : ℕ, Subgroup.zpowers (PadicMeasure.unitsToZModPow p n u) = ⊤`
  — `u` is a *topological generator* of `ℤ_[p]ˣ` (every finite-level reduction
  generates). **Crucially, the proof invokes `hgen` only at `n = 1`** (line 140:
  `hgen 1`). The full tower is over-strong for this conclusion.

Conclusion: `IsPrimitiveRoot (PadicInt.teichmuller p u) (p − 1)`.

Proof shape (≈12 lines, all standard order-theory):
```lean
rw [IsPrimitiveRoot.iff_orderOf]                       -- reduce to orderOf ω(u) = p−1
have hpow : ω(u)^(p−1) = 1 := … teichmullerFun_pow_card_sub_one …   -- Fermat
have hdvd1 : orderOf ω(u) ∣ p−1 := orderOf_dvd_of_pow_eq_one hpow
have ho1 : orderOf (unitsToZModPow p 1 u) = p−1 :=
  … orderOf_eq_card_of_forall_mem_zpowers (hgen 1) … ZMod.card_units_eq_totient … Nat.totient_prime …
have hred : unitsToZModPow p 1 ω(u) = unitsToZModPow p 1 u := … teichmullerFun_sub_self_mem …
have hdvd2 : p−1 ∣ orderOf ω(u) := … orderOf_map_dvd …
exact Nat.dvd_antisymm hdvd1 hdvd2
```

---

### Size classification (Phase 2a)

Verdict: **SMALL** (as a stated proposition; the *mathematical content* it
witnesses is BIG — see below).

Reason: the proof is a short, mechanical two-sided-divisibility argument
(`orderOf ω(u) ∣ p−1` via Fermat; `p−1 ∣ orderOf ω(u)` because ω is a section of
reduction and the reduction generates). It is a *corollary* of two facts: (i) the
Teichmüller lift kills `(p−1)`-powers (already a project lemma
`teichmullerFun_pow_card_sub_one`), and (ii) a generator of `(ZMod p)ˣ` has order
`p−1`. As a packaged statement it is a one-paragraph order computation, not a deep
theorem.

But note the *content it witnesses* — "`ℤ_[p]` contains a primitive `(p−1)`-th
root of unity, realised as the Teichmüller lift of a generator" — is a **headline
structural fact** of p-adic number theory (Hensel/Teichmüller, the prime-to-`p`
torsion of `ℤ_[p]ˣ`). That is what makes the *content* mathlib-worthy; the
specific wrapper here is the SMALL part.

(Literature width is EXHAUSTIVE regardless of BIG/SMALL — recorded for framing.)

### One-line check (Phase 2b)

Body line count: ~12 substantive lines.
Kind: `theorem`.
One-liner verdict: **n/a** — kind is `theorem`, not `def`/`abbrev`/`structure`.
The one-line-definition exemption machinery (defeq-abuse / diamond-avoidance /
API-stability) does not apply to propositions.

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                              | Hit? | Standard form found                                            | Notes |
|----|----------------------------------|----------------------------------------------------------------------------------------------------|------|----------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | Teichmüller lift of generator of `(Z/p)^×` is primitive `(p−1)`-th root of unity in `Z_p`          | yes  | `ω : F_p^× → μ_{p−1} ⊂ Z_p^×` iso; ω of a generator generates μ_{p−1} | K. Conrad "teichmuller.pdf"; Washington *Cyclotomic Fields* §2 (ω); Neukirch *ANT* II.§7 |
|  2 | WebSearch (general form)         | roots of unity in `Z_p` / complete DVR; `μ(K) ≅ μ(residue field)` prime-to-p part; Hensel lift     | yes  | for a complete DVR with residue field `k`, the prime-to-`p` roots of unity lift uniquely & isomorphically from `k^×` (Teichmüller) | Serre *Local Fields*; Neukirch II.§7 Prop 7.x; "the `(p−1)`-th roots of unity in `Z_p`" is canonical |
|  3 | WebSearch (named-after / aliases)| "Teichmüller representatives" / "Teichmüller character" / "multiplicative representatives" `Z_p`    | yes  | Teichmüller character ω of conductor `p`, values the `(p−1)`-th roots of unity; ω(a) primitive ⇔ a generates `F_p^×` | standard in Iwasawa theory & p-adic L-functions (the exact §5/§7 context of this project) |
|  4 | ChatGPT MCP                      | "standard form + maximal generality + historical formulation of: Teichmüller lift of an `F_p^×` generator is a primitive `(p−1)`-th root in `Z_p`" | **n/a** | — | `chatgpt-math` MCP not loaded/callable in this session (no matching deferred tool; auth-gated). Recorded attempted-unavailable; covered by 6 corroborating channels below. |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/`                           | **n/a** | (no references dir) | both `…/.mathlib-quality/references/` and the shared `refs/` store are **absent** in this checkout — recorded n/a. In-source RJW pointer: Def 5.15 (ω as Teichmüller lift), §5.2 determinacy. |
|  6 | nLab                             | Teichmüller lift / Witt vectors / roots of unity in p-adic integers                                | partial | nLab "Teichmüller representative" / "Witt vectors" cover the lift `k^× → W(k)^×`; the `Z_p` specialisation is the `W(F_p)=Z_p` case | nLab frames it via Witt vectors (matches mathlib's `Perfection.teichmuller`); the primitive-root corollary is folklore there |
|  7 | nCatLab (categorical)            | (categorical angle)                                                                                | **n/a** | — | not a higher-categorical statement — it is a concrete order/section fact about one unit; nothing to look up |
|  8 | Stacks Project (alg geom)        | Teichmüller lift / roots of unity in complete local ring / Witt vectors                            | partial | Stacks has Witt vectors & complete-local-ring theory (tag 0AMC etc.); the Teichmüller lift `k^× → A^×` for `A` complete with residue `k` is there as Hensel-lifting of `Xⁿ−1` | the "lift of a generator is a generator of μ" corollary is immediate from uniqueness of the lift |
|  9 | MathOverflow / Math.StackExchange| "roots of unity in `Z_p`", "Teichmüller character primitive", "(p−1)-th roots of unity p-adic"     | yes  | many answers: `μ(Z_p) = μ_{p−1}` (p odd); ω restricts to an iso `F_p^× ≅ μ_{p−1}`; generator ↦ primitive root | standard MO/MSE folklore; consistent with rows 1–3 |
| 10 | recent arXiv (last 5 years)      | Teichmüller / p-adic roots-of-unity **formalization** (Lean / mathlib), 2021–2025                  | yes (formalization status) | content classical; mathlib has the **Witt/Perfection Teichmüller** + `HasEnoughRootsOfUnity (ZMod p) (p−1)`, but **no `HasEnoughRootsOfUnity Z_p (p−1)`** and no "lift of generator is primitive root in `Z_p`" | confirms the precise mathlib gap (see Phase 5); the AINTLIB sibling project is itself the closest formalization on record |

**Protocol pass check.** WebSearch ran 3 distinct queries at three generality
levels (rows 1–3: the exact statement; the general complete-DVR `μ(K)≅μ(k)`
prime-to-p form; the named "Teichmüller character/representatives" form). ChatGPT
MCP recorded `n/a` with a concrete reason and the loss is compensated by ≥6
independent corroborating channels. Local refs checked (absent → n/a). nLab,
Stacks, MathOverflow checked (hits/partial). nCatLab `n/a` with reason. arXiv
formalization-status checked. No channel silently skipped.

### Literature summary (Phase 3)

Concept identified as: **the Teichmüller lift sends a generator of `(ZMod p)ˣ`
to a primitive `(p−1)`-th root of unity in `ℤ_[p]`** — equivalently, the
Teichmüller character `ω : F_p^× → μ_{p−1} ⊂ ℤ_[p]ˣ` is a group isomorphism, so
it carries generators to generators (= primitive roots). Special case of the
general fact that for a complete DVR `A` with residue field `k` of characteristic
`p`, the prime-to-`p` roots of unity of `A` lift uniquely and isomorphically from
`k^×` (Hensel/Teichmüller). For `A = ℤ_[p]`, `k = F_p`, this gives `μ_{p−1} ⊂
ℤ_[p]` with ω an iso `F_p^× ≅ μ_{p−1}`.

Sources agree on the standard form: **yes, unanimously** — K. Conrad, Washington
(*Cyclotomic Fields*), Neukirch (*ANT* II.§7), Serre (*Local Fields*), the Stacks
Project (Witt-vector formulation), and standard MO/MSE folklore all state it
identically. The only variation is the *ambient ring* (just `ℤ_[p]` vs. a general
complete DVR) and *how the generator is supplied* (a plain generator of `F_p^×`,
universally — never a "tower of finite-level reductions").

Most general standard form: for a complete DVR `A`, residue field `k` of
characteristic `p`, the Teichmüller lift `k^× → A^×` is a section of reduction and
restricts to an isomorphism onto the prime-to-`p` roots of unity; in particular
the lift of a generator of `k^×` (when `k` is finite) is a primitive `(#k − 1)`-th
root of unity.

Generality dimensions where the literature varies:
  - **ambient ring**: `ℤ_[p]` (user) → general complete DVR / unramified
    extension with finite residue field. The user's form is the base `A = ℤ_[p]`.
  - **how the generator is given**: a plain generator `g` of `(ZMod p)ˣ` (the
    universal phrasing) vs. the user's project-specific *infinite tower*
    `∀ n, zpowers(unitsToZModPow p n u) = ⊤`. **The literature never uses the
    tower** — and the proof here doesn't either (only `n = 1`).

Disagreement with the literature: **none on the mathematics.** The statement is
exactly the standard fact, but encoded with a needlessly strong and
project-specific hypothesis. This is the opposite of the "empty Phase 3 ⇒
BORDERLINE" failure mode — the literature is rich and unanimous; the issue is the
*form*, handled in Phase 4.

---

### Generality analysis — `PadicLFunctions.teichmuller_isPrimitiveRoot` (Phase 4)

Literature-standard form (Phase 3): for a complete DVR `A` with finite residue
field `k` of char `p`, the Teichmüller lift of a **generator of `k^×`** is a
primitive `(#k − 1)`-th root of unity. The minimal hypothesis is *"the reduction
mod the maximal ideal generates `k^×`"* — a single, level-`1` condition.

| # | Parameter / hypothesis                              | Current Lean form                                                   | Literature-standard form                              | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------------------------|---------------------------------------------------------------------|-------------------------------------------------------|---------------------|----------------------------------|
| 1 | the generator hypothesis `hgen`                     | `∀ n, zpowers(unitsToZModPow p n u) = ⊤` (**full infinite tower**)  | a single generator `g` of `(ZMod p)ˣ`, or "`u mod p` generates" | **yes — DECISIVE** | the proof uses **only `hgen 1`** (line 140); levels `n ≥ 2` are dead weight. The honest hypothesis is `Subgroup.zpowers (unitsToZModPow p 1 u) = ⊤`, i.e. `u mod p` generates `(ZMod p)ˣ`. CHEAP to weaken (delete the `∀ n`, keep `n=1`). |
| 2 | input `u : ℤ_[p]ˣ` + reduction via `unitsToZModPow`  | a p-adic unit, reduced by the project map `PadicMeasure.unitsToZModPow` | the residue `u mod p ∈ (ZMod p)ˣ` (any generator)     | yes                 | `unitsToZModPow` is a project-defined `Units.map (toZModPow n)`; the literature & the sibling lemma take the generator directly in `(ZMod p)ˣ`. Stating the result over `ℤ_[p]ˣ` + the project map is a narrowing of "feed me a generator of `(ZMod p)ˣ`". |
| 3 | the Teichmüller map `PadicInt.teichmuller`           | project-local `ℤ_[p]ˣ →* ℤ_[p]ˣ` (`Interpolation/Branches.lean:178`) | mathlib `Perfection.teichmuller₀` (Witt/perfection)   | reformulation       | the project's `teichmuller` is *built on* `Perfection.teichmuller₀` (via `teichmullerZMod`) but is a distinct project def; the mathlib-idiomatic statement is about the mathlib map or the `ZMod p →*₀ ℤ_[p]` packaging (= the sibling's `teichmuller`). See Phase 4c. |
| 4 | ambient ring `ℤ_[p]`                                | the p-adic integers                                                 | any complete DVR / unramified extension, finite residue field | yes (in principle)  | the prime-to-`p` lift fact generalises to complete DVRs; but this is an EXPENSIVE re-development (general Teichmüller-section API). Does **not** downgrade the verdict (Bourbaki 2.0); informs sequencing only. |
| 5 | conclusion exponent `p − 1`                          | `p − 1`                                                             | `#k − 1` (here `#F_p − 1 = p − 1`)                    | NO (already exact)  | for residue field `F_p` this is exactly `#k − 1`; nothing weaker makes sense. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD**, primarily along axis 1
(the hypothesis is the full tower when only `n = 1` is used and needed) and axis 2
(stated over `ℤ_[p]ˣ` + the project reduction map rather than a plain generator of
`(ZMod p)ˣ`).

Number of weakening opportunities found: **K = 2 decisive + CHEAP** (axes 1, 2) +
1 reformulation (axis 3, primitives) + 1 EXPENSIVE optional (axis 4, ambient
ring). Because K ≥ 1 *cheap* weakening exists, this is **not** `YES-add-as-is`.

Proposed restatement (CHEAP — drop the tower, take a clean generator):
```lean
theorem teichmuller_isPrimitiveRoot {g : (ZMod p)ˣ}
    (hg : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) :
    IsPrimitiveRoot (PadicInt.teichmullerZMod p (g : ZMod p)) (p - 1)
```
This is **exactly** the sibling `FltRegularBernoulli.teichmuller_isPrimitiveRoot_of_generator`
(`Characters.lean:188`). Cost: **CHEAP** — the proof is essentially the existing
one with `hgen 1` replaced by `hg` and `unitsToZModPow p 1` replaced by direct
`toZMod` (the sibling already does it in ~10 lines).

Cost of the EXPENSIVE general-DVR restatement (axis 4): high (general
Teichmüller-section API) — a *separate, later* PR; does not gate this one and
does not downgrade the verdict.

### Modern-idiom check (Phase 4c — Bourbaki 2.0)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" → typeclasses? | **YES** | replace the bespoke `∀ n, zpowers(unitsToZModPow …) = ⊤` tower with the existing mathlib `IsCyclic (ZMod p)ˣ` (true via `ZMod.isCyclic_units_prime`) + `IsCyclic.exists_generator`; the headline is then the **`HasEnoughRootsOfUnity ℤ_[p] (p−1)` instance**, with the primitive-root lemma as its `prim` field | a typeclass instance composes with all of mathlib's roots-of-unity / cyclotomic / Dirichlet-orthogonality API (`HasEnoughRootsOfUnity` powers `DirichletCharacter.Orthogonality`, cyclotomic-Galois, finite-abelian duality) |
|  2 | sequences/metric → filters/topological? | no | n/a (no sequences) | — |
|  3 | construct object where a primitive should be characterised? | **partially** | the result is *about* the project-local `PadicInt.teichmuller`; the mathlib-idiomatic carrier is mathlib's `Perfection.teichmuller₀` (or the `ZMod p →*₀ ℤ_[p]` packaging), of which the project def is a wrapper | reusing mathlib's Witt/perfection Teichmüller avoids a second `Z_p` Teichmüller def in mathlib |
|  4 | set-with-predicate → bundled substructure? | no | the conclusion is already the bundled `IsPrimitiveRoot` predicate | — |
|  5 | field/metric-specific → weaken typeclass? | **YES (= axis 4)** | `ℤ_[p]` → complete DVR with finite residue field | general prime-to-`p`-roots-of-unity lift theory |
|  6 | 1-categorical → higher-categorical? | no | — | — |
|  7 | concrete index → general structure? | no | `p − 1 = #F_p − 1` is already the right index | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** (rows 1 and 5, with row 3 as the carrier).
  - The mathlib-canonical contribution is **not** this `unitsToZModPow`-tower
    lemma but the instance **`HasEnoughRootsOfUnity ℤ_[p] (p − 1)`** (resp.
    `instExistsPrimitiveRoot`), proved by combining mathlib's
    `ZMod.isCyclic_units_prime` + `IsCyclic.exists_generator` with the
    "Teichmüller-lift-of-generator-is-primitive-root" lemma stated over a plain
    generator (axis 1). This is *precisely* what the sibling
    `FltRegularBernoulli` does (`Characters.lean:206–209`:
    `instance : HasEnoughRootsOfUnity ℤ_[p] (p − 1)`).
  - Cost: **CHEAP** (the proof exists, in two places, and is short).
  - Real mathematical improvement (not "looks cooler"): mathlib already has
    `HasEnoughRootsOfUnity (ZMod p) (p − 1)` (`RingTheory/ZMod/Torsion.lean:27`)
    but **lacks the `ℤ_[p]` analogue**, even though it is the more useful one for
    the Iwasawa-theory / p-adic-L-function / Dirichlet-orthogonality stack that
    *consumes* `HasEnoughRootsOfUnity`. Supplying it as an instance unlocks
    `DirichletCharacter` orthogonality and character-sum machinery valued in
    `ℤ_[p]` (the exact §5.2 determinacy use the project cites).

Because Phase 4b found a CHEAP literature-weakening (axis 1/2) AND Phase 4c finds
a real modern-idiom improvement (instance form), Phase 7 takes
**`YES-but-generalise-first`** (reasons: LITERATURE-WEAKENING + MODERN-IDIOM +
DEDUP).

---

### Diamond / defeq risk (Phase 4.5) — `PadicLFunctions.teichmuller_isPrimitiveRoot`

**n/a — declaration kind is `theorem`.** No definitional equalities, no
typeclass-search paths introduced. (Note: the *proposed* `HasEnoughRootsOfUnity
ℤ_[p] (p−1)` instance form *would* warrant an instance-diamond check — but that is
a Phase-4.5 item for the restated instance, not for this theorem.)

---

### Mathlib search-status (Phase 5) — `PadicLFunctions.teichmuller_isPrimitiveRoot`

Five-method exhaustive search, on the user's form AND the literature-standard
generator form AND the modern-idiom instance form:

[A] **Lean-Finder** — `n/a` — Lean-Finder MCP not available in this session (recorded n/a, not blank).
[B] **Loogle** — `IsPrimitiveRoot _ (_ - 1)`; `IsPrimitiveRoot (teichmuller _ _) _`; `HasEnoughRootsOfUnity ℤ_[_] _` — `n/a` — `lean_loogle` MCP not loaded; **substituted by exhaustive source grep over `.lake/packages/mathlib/Mathlib/`** (results below).
[C] **LeanSearch** — "Teichmüller lift of generator is primitive root"; "roots of unity in p-adic integers"; "Z_p has enough roots of unity" — `n/a` — `lean_leansearch` MCP not loaded; substituted by source grep.
[D] **Grep mathlib source** — exhaustive over `.lake/packages/mathlib/Mathlib/`:
  - `teichmuller`/`teichmüller` → **only** `Order/TeichmullerTukey.lean` (unrelated, the Teichmüller–Tukey lemma) and `RingTheory/Teichmuller.lean` (`Perfection.teichmuller`/`teichmuller₀` — the **general Witt/perfection lift** `Perfection (R⧸I) p →*₀ R`, **no `ℤ_[p]`-specific primitive-root statement, no `(p−1)`-th-root corollary**).
  - `HasEnoughRootsOfUnity` for `ℤ_[p]` → **NONE.** Mathlib has `HasEnoughRootsOfUnity (ZMod p) (p−1)` (`RingTheory/ZMod/Torsion.lean:27`), `Circle`, separably/algebraically-closed fields — **but no `ℤ_[p]` / complete-DVR instance.**
  - `IsPrimitiveRoot … (p − 1)` in a p-adic / `PadicInt` context → **NONE.** The `IsPrimitiveRoot` hits are cyclotomic-field / `ZMod` / number-field, never `ℤ_[p]`.
  - "generator of `(ZMod p)ˣ` ⇒ primitive root anywhere" → **no general lemma**; the residue-field version is `ZMod.rootsOfUnity_eq_top` (about `ZMod p` itself), not a lift to `ℤ_[p]`.
[E] **Name pattern (grep)** — `teichmuller`, `primitiveRoot.*[Pp]adic`, `[Pp]adic.*primitiveRoot`, `rootsOfUnity.*ℤ_`, `unitsToZModPow` over mathlib — **no hit for the p-adic primitive-root / Teichmüller-lift statement.** (`unitsToZModPow` is a *project* name; absent from mathlib.)

**Building blocks present in mathlib** (so the dedup'd statement is *composable
internally*, but is not itself a ≤3-call mathlib composition — see Phase 6):
  - `IsPrimitiveRoot.iff_orderOf`, `IsPrimitiveRoot.orderOf`, `IsPrimitiveRoot.eq_orderOf` (`RingTheory/RootsOfUnity/PrimitiveRoots.lean:203–223`).
  - `orderOf_eq_card_of_forall_mem_zpowers` (`GroupTheory/SpecificGroups/Cyclic/Basic.lean:201`); `orderOf_dvd_of_pow_eq_one`; `orderOf_map_dvd`.
  - `ZMod.card_units_eq_totient`, `Nat.totient_prime`, `ZMod.isCyclic_units_prime`, `IsCyclic.exists_generator`.
  - `Perfection.teichmuller₀` + `ZMod.pow_card_sub_one_eq_one` (the Fermat input).
  - `HasEnoughRootsOfUnity (ZMod p) (p−1)` — the **residue-field** analogue of exactly the instance we want for `ℤ_[p]`.

Searched for both/all three forms:
  - user's form (`unitsToZModPow`-tower hypothesis, project `PadicInt.teichmuller`) — **absent**;
  - literature-standard generator form (`{g : (ZMod p)ˣ} → IsPrimitiveRoot (ω g) (p−1)`) — **absent from mathlib** (present *in this repo* as the sibling `FltRegularBernoulli.teichmuller_isPrimitiveRoot_of_generator`);
  - modern-idiom instance form (`HasEnoughRootsOfUnity ℤ_[p] (p−1)`) — **absent from mathlib** (present in this repo as `FltRegularBernoulli`'s instance).

Concluded: **not in mathlib** (the methods genuinely unavailable as MCP tools —
A/B/C — are recorded `n/a`; the authoritative grep D/E over the vendored mathlib
source is exhausted and returns nothing for any of the three forms). Mathlib has
the *general Witt Teichmüller* and the *residue-field* `HasEnoughRootsOfUnity`,
but **not** the `ℤ_[p]` primitive-root / lift statement in any form.

---

### Call sites (Phase 6.0) — `PadicLFunctions.teichmuller_isPrimitiveRoot`

Internal use count (this project, excluding the declaring line and
comment/docstring mentions): **1**.
External-to-file callers: **0** distinct files (within `PadicLFunctions`).
Cross-project siblings: **a near-duplicate exists and is used 4×** in
`FltRegularBernoulli`.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `ResidueZeta.lean:173` | `rw [(teichmuller_isPrimitiveRoot p hgen).eq_orderOf]` — inside `norm_teichmuller_pow_sub_one_eq_one`, to get `orderOf ω(u) = p−1` and conclude `¬(p−1 ∣ i)` for `0<i<p−1` |
| `ResidueZeta.lean:158` | docstring mention only (not a call) |
| `FltRegularBernoulli/.../Characters.lean:188` | **sibling theorem `teichmuller_isPrimitiveRoot_of_generator`** — same content, *generator* hypothesis, project-clean form |
| `FltRegularBernoulli/.../Characters.lean:210,259`; `HMinus/.../Teichmuller.lean:429,448` | the **sibling** is used 4× (feeds `HasEnoughRootsOfUnity ℤ_[p] (p−1)` and character-order facts) |

What the call-sites pattern tells you (per the Phase-6 signal table):
**K = 1 internal use** of *this* declaration → "possibly the wrong abstraction;
leans toward generalise/dedup, not add-as-is". Decisively, the *same mathematical
fact* is independently formalised in a **sibling project** with a cleaner
hypothesis and is used 4× there to build the very `HasEnoughRootsOfUnity ℤ_[p]
(p−1)` instance that Phase 4c identifies as the right mathlib target. So the
honest reading is: this is **one of two copies** of a canonical fact; the
upstreaming target is the *single, deduplicated, generator-hypothesis* statement
(packaged as the instance), not either project-local wrapper.

---

### Composition check (Phase 6) — `PadicLFunctions.teichmuller_isPrimitiveRoot`

Can the declaration be derived from **mathlib** in ≤3 chained calls?

Attempt 1: `IsPrimitiveRoot.iff_orderOf` + a mathlib "orderOf ω(u) = p−1".
  - Mathlib decls: `IsPrimitiveRoot.iff_orderOf`, `orderOf_eq_card_of_forall_mem_zpowers`, `ZMod.card_units_eq_totient`, `Nat.totient_prime`.
  - Result: **fails as a ≤3-call composition.** Getting `orderOf ω(u) = p−1`
    requires *both* the upper bound (`orderOf ∣ p−1` via the project lemma
    `teichmullerFun_pow_card_sub_one`) *and* the lower bound (`p−1 ∣ orderOf`,
    via `ω` being a section of reduction — the project lemma
    `teichmullerFun_sub_self_mem` plus `orderOf_map_dvd`), then a `Nat.dvd_antisymm`.
    That is a genuine two-sided-divisibility argument over **project-local**
    Teichmüller lemmas — not a mathlib one-liner.

Attempt 2: reuse mathlib's `Perfection.teichmuller₀` directly.
  - Result: **fails** — mathlib's Teichmüller has no primitive-root corollary and
    no `ℤ_[p]ˣ →* ℤ_[p]ˣ` packaging; the project had to build `PadicInt.teichmuller`,
    `teichmullerFun_pow_card_sub_one`, `teichmullerFun_sub_self_mem` on top of it.
    The proof depends on those project lemmas, which are themselves not in mathlib.

Conclusion: **NOT-COMPOSABLE from mathlib** (it composes only from
*project-local* Teichmüller API + mathlib order theory). Phase 7 therefore
considers the YES verdicts, not `NO-composable-from-mathlib`. (And it is **not**
`NO-mathlib-has-it`: mathlib has neither the statement nor the `ℤ_[p]`-Teichmüller
section it rests on.)

---

## Verdict: `PadicLFunctions.teichmuller_isPrimitiveRoot`

**Category:** `YES-but-generalise-first`

**Evidence:**
- **Literature (Phase 3):** the Teichmüller lift of a generator of `(ZMod p)ˣ` is
  a primitive `(p−1)`-th root of unity in `ℤ_[p]` — canonical, unanimously stated
  (K. Conrad, Washington, Neukirch, Serre, Stacks/Witt formulation, MO/MSE). ≥6
  corroborating channels (rows 1,2,3,6,8,9); ChatGPT MCP n/a with reason.
- **Generality (Phase 4):** **STRICTLY NARROWER** — the hypothesis is the full
  infinite tower `∀ n, zpowers(unitsToZModPow p n u) = ⊤` but the proof uses only
  `n = 1` (CHEAP weakening to a single generator of `(ZMod p)ˣ`), and is phrased
  over the project map `unitsToZModPow` and the project def `PadicInt.teichmuller`.
- **Modern idiom (Phase 4c):** the mathlib-canonical carrier is the **instance
  `HasEnoughRootsOfUnity ℤ_[p] (p − 1)`** (mathlib has the residue-field
  `HasEnoughRootsOfUnity (ZMod p) (p−1)` but **not** the `ℤ_[p]` one), built from
  `ZMod.isCyclic_units_prime` + the dedup'd primitive-root lemma. CHEAP, with real
  downstream payoff (Dirichlet-orthogonality / character sums valued in `ℤ_[p]`).
- **Mathlib search (Phase 5):** **not in mathlib** in any of the three forms;
  building blocks present but the `ℤ_[p]`-Teichmüller section it rests on is also
  absent from mathlib.
- **Composition (Phase 6):** **NOT-COMPOSABLE from mathlib** — composes only from
  project-local Teichmüller lemmas.
- **Dedup (Phase 6.0):** a cleaner sibling `FltRegularBernoulli.teichmuller_
  isPrimitiveRoot_of_generator` (`Characters.lean:188`) already states the same
  fact over a generator hypothesis and feeds a `HasEnoughRootsOfUnity ℤ_[p] (p−1)`
  instance — used 4× there. This declaration is the *second copy*.

**Rationale.**
The content is unquestionably mathlib-worthy: that `ℤ_[p]` contains a primitive
`(p−1)`-th root of unity, realised as the Teichmüller lift of a generator of
`(ZMod p)ˣ`, and hence `HasEnoughRootsOfUnity ℤ_[p] (p−1)`. Mathlib has the
*residue-field* analogue (`RingTheory/ZMod/Torsion.lean`) and the *general Witt*
Teichmüller (`RingTheory/Teichmuller.lean`) but **not** this `ℤ_[p]`-level fact in
any form — confirmed by exhaustive grep over `Mathlib/`. The verdict is
*generalise-first* rather than *add-as-is* for three concrete, evidence-backed
reasons. (1) **Hypothesis is over-strong and project-specific (Phase 4, axis 1):**
the `∀ n` tower is dead weight — `hgen` is invoked only at `n = 1`; the honest,
literature-matching hypothesis is "`u mod p` generates `(ZMod p)ˣ`", i.e. a single
generator. (2) **It should be an instance, not a tower-lemma (Phase 4c):** the
mathlib idiom is `HasEnoughRootsOfUnity ℤ_[p] (p − 1)` obtained via
`ZMod.isCyclic_units_prime` + `IsCyclic.exists_generator` — composing with
mathlib's roots-of-unity/Dirichlet-orthogonality machinery that consumes that
class. (3) **It is a duplicate (Phase 6.0):** the sibling project already has the
clean generator-form statement *and* the instance. The right upstreaming move is a
**single, deduplicated** contribution — the generator-hypothesis lemma plus the
`HasEnoughRootsOfUnity ℤ_[p] (p − 1)` instance — replacing both project copies,
stated over mathlib's Teichmüller (or a shared `Common/` `ZMod p →*₀ ℤ_[p]`
packaging). The `unitsToZModPow`-tower phrasing here is a §7-internal convenience
(it matches the topological-generator hypothesis used elsewhere in `ResidueZeta`)
and should *not* be the mathlib statement; instead, `ResidueZeta`'s single call
site (`norm_teichmuller_pow_sub_one_eq_one`) can derive the tower form from the
generator form in one extra line (`hgen 1`).

**Reason for the generalisation:**
  - **LITERATURE-WEAKENING (CHEAP):** replace `∀ n, zpowers(unitsToZModPow p n u)
    = ⊤` with a single generator `g` of `(ZMod p)ˣ` (the only level the proof
    uses) — exactly the sibling's hypothesis.
  - **MODERN-IDIOM / Bourbaki 2.0 (CHEAP):** package the result as the instance
    `HasEnoughRootsOfUnity ℤ_[p] (p − 1)` (the `ℤ_[p]` analogue of mathlib's
    existing residue-field instance), so it composes with mathlib's character /
    cyclotomic API.
  - **DEDUP:** merge with `FltRegularBernoulli.teichmuller_isPrimitiveRoot_of_
    generator` and its `HasEnoughRootsOfUnity ℤ_[p] (p−1)` instance into one
    shared declaration; do not upstream two copies.
  - (Optional, **EXPENSIVE, later**) generalise the ambient ring from `ℤ_[p]` to a
    complete DVR with finite residue field — a separate PR; does not gate this one
    and does not downgrade the verdict (Bourbaki 2.0).

Proposed restatement (the mathlib-idiomatic, deduplicated target):
```lean
-- A shared place (Common/ in AINTLIB; Mathlib/NumberTheory/Padics/Teichmuller.lean upstream).

/-- The Teichmüller lift of a generator of `(ZMod p)ˣ` is a primitive
`(p−1)`-th root of unity in `ℤ_[p]`. -/
theorem PadicInt.teichmuller_isPrimitiveRoot_of_generator {p : ℕ} [Fact p.Prime]
    {g : (ZMod p)ˣ} (hg : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) :
    IsPrimitiveRoot (PadicInt.teichmullerZMod p (g : ZMod p)) (p - 1) := by
  refine ⟨?_, fun l hl => ?_⟩
  · rw [← map_pow, ← Units.val_pow_eq_pow_val, ZMod.units_pow_card_sub_one_eq_one,
      Units.val_one, map_one]
  · have h_units : g ^ l = 1 := Units.ext <| by
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact teichmullerZMod_injective (by rwa [map_pow, map_one])
    have h_order : orderOf g = p - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
    rw [← h_order]; exact orderOf_dvd_of_pow_eq_one h_units

/-- `ℤ_[p]` contains enough `(p−1)`-th roots of unity. -/
instance PadicInt.instHasEnoughRootsOfUnity {p : ℕ} [Fact p.Prime] :
    HasEnoughRootsOfUnity ℤ_[p] (p - 1) where
  prim := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
    exact ⟨_, PadicInt.teichmuller_isPrimitiveRoot_of_generator hg⟩
  -- (the FltRegularBernoulli instance is the ready-made template)
```
(The `ResidueZeta` call site then becomes `(teichmuller_isPrimitiveRoot_of_
generator (hgen' )).…` where `hgen'` is the `n=1` consequence of the local tower
hypothesis.)

Estimated cost of regeneralisation: **CHEAP** — the deduplicated proof already
exists, twice, in this repo (the sibling lemma + instance). The work is: (a)
weaken the hypothesis to a single generator (delete the `∀ n`), (b) move the
shared statement + `HasEnoughRootsOfUnity ℤ_[p] (p−1)` instance into a common
location, (c) re-route both projects' call sites. The EXPENSIVE complete-DVR
generalisation is explicitly *out of scope* for this first step.

Mathlib downstream this enables (MODERN-IDIOM, REQUIRED):
  - The instance **`HasEnoughRootsOfUnity ℤ_[p] (p − 1)`** — currently **absent**
    (mathlib has only `HasEnoughRootsOfUnity (ZMod p) (p − 1)`). This is the
    prerequisite for `DirichletCharacter.Orthogonality` and character-sum
    arguments valued in `ℤ_[p]` (mathlib's orthogonality file is *parametrised* by
    exactly `[HasEnoughRootsOfUnity R (Monoid.exponent (ZMod n)ˣ)]`).
  - A reusable "primitive `(p−1)`-th root in `ℤ_[p]`" / `μ_{p−1} ⊂ ℤ_[p]^×`
    statement that composes with mathlib's cyclotomic and `IsPrimitiveRoot` API —
    the backbone of the p-adic-L-function / Iwasawa programme both AINTLIB
    projects pursue.

Next action: **`/generalise PadicLFunctions.teichmuller_isPrimitiveRoot`** to
produce the single-generator restatement, then **deduplicate against
`FltRegularBernoulli.teichmuller_isPrimitiveRoot_of_generator`** (lift the shared
statement + `HasEnoughRootsOfUnity ℤ_[p] (p−1)` instance into `Common/`), and
finally upstream that one instance + lemma — *not* the `unitsToZModPow`-tower
wrapper.

---

## Next step

Run `/generalise PadicLFunctions.teichmuller_isPrimitiveRoot` to (1) drop the
over-strong `∀ n` tower hypothesis down to a single generator of `(ZMod p)ˣ` (the
only level the proof uses), and (2) restate the content as the instance
`HasEnoughRootsOfUnity ℤ_[p] (p − 1)`. Then deduplicate with the existing sibling
`FltRegularBernoulli.teichmuller_isPrimitiveRoot_of_generator` (+ its instance) by
moving one shared declaration into `Common/`. Upstream that single deduplicated
lemma + instance; do not PR the project-specific tower form.
