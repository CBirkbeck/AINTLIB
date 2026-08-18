# `/mathlibable` report — `PadicLFunctions.stabilisedEisenstein`

**Final verdict: `YES-but-generalise-first`**
(reason: LITERATURE-WEAKENING + MODERN-IDIOM — the content is the standard Hida/Wiles
p-stabilised Eisenstein series and genuinely belongs in mathlib, but it is currently stated
for a *fixed prime* `p` on top of a project-local level-raising / subgroup-restriction stack
that is not yet in mathlib; the dependency stack must be upstreamed and the statement
generalised before a PR.)

---

### Baseline (Phase 0)

- lake build:               build NOT re-run (stale/slow per task note); **reasoned from source** — Phase 0 fallback.
- decl `PadicLFunctions.stabilisedEisenstein`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/EisensteinComplex.lean:335`
- kind:                      `def` (`noncomputable def`)
- has sorry:                 no (the def and its two consumer theorems `stabilisedEisenstein_apply`, `stabilisedEisenstein_smul_apply` are sorry-free; the supporting `stabilisedDiff_slash_mapGL` etc. are complete proofs)
- module docstring summary:  the q-expansion of the p-stabilised Eisenstein series (RJW §8, complex side): `E_k`, its p-stabilisation `E_k − p^{k−1}E_k(p·)`, and its Γ₀(p)-modularity via the LeanModularForms level-raising operator.

---

### Statement (Phase 1)

`PadicLFunctions.stabilisedEisenstein` is **a definition** of the following object:

> Fix a prime `p` and a weight `k ≥ 3`. The **p-stabilised Eisenstein series**
> `E_k^{(p)}(z) := E_k(z) − p^{k−1} E_k(pz)` is a holomorphic modular form of weight `k`
> for the Hecke congruence group `Γ₀(p)` (realised inside `GL₂(ℝ)` as the image of
> `Γ₀(p) ≤ SL₂(ℤ)` under `mapGL ℝ`). Here `E_k` is mathlib's level-1 normalised
> Eisenstein series `ModularForm.E` (constant term `1`).

Construction (Lean side): it bundles a `ModularForm ((Gamma0 p).map (mapGL ℝ)) (k : ℤ)`:
- `toFun := ⇑(stabilisedDiff p hk)` — the underlying function is `E_k − p^{k−1}·(levelRaiseFun p k E_k)`, and `levelRaiseFun p k f` is `(p:ℂ)^{1−k} • (f ∣[k] α_p)` with `α_p = [[p,0],[0,1]]`, i.e. `(ι_p f)(z) = f(pz)` (Miyake §4.6 Lem 4.6.1). So `toFun z = E_k(z) − p^{k−1} E_k(pz)` (proved as `stabilisedEisenstein_apply`).
- `slash_action_eq'` — Γ₀(p)-invariance, the mathematical heart, discharged by `stabilisedDiff_slash_mapGL` (down-conjugation bridge `slash_mapGL_levelRaiseFun` + `levelRaiseConjOfDvd_mem_Gamma0`).
- `holo'` — inherited from `stabilisedDiff`.
- `bdd_at_cusps'` — boundedness at the cusps of Γ₀(p), transferred from Γ₁(p·1) because both are arithmetic and hence share the SL₂(ℤ)-cusps (`Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z`).

Variables / typeclasses involved (Lean side):
- `(p : ℕ)` with `[hp : Fact p.Prime]` — a **fixed prime** (section variable). The prime is baked into the definition, not a free modulus.
- `{k : ℕ}` `(hk : 3 ≤ k)` — weight, with the convergence bound `k ≥ 3` (Eisenstein-series absolute convergence).
- `NeZero p` derived locally from primality.

Hypotheses (Lean side): `hk : 3 ≤ k`.

Conclusion (math): `E_k^{(p)}` is a weight-`k` modular form for `Γ₀(p)`.

Conclusion (Lean): `ModularForm ((Gamma0 p).map (mapGL ℝ)) (k : ℤ)` — n/a beyond this; it is a definition (constructs an element of the modular-forms type).

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: it constructs a *named mathematical object* (the p-stabilised Eisenstein series, a level-Γ₀(p) modular form) that is a primary deliverable of the file's docstring ("Main" object: `see stabilisedEisenstein`, the genuine `ModularForm ((Gamma0 p).map (mapGL ℝ)) k`); the underlying p-stabilisation is a classically-named construction (Hida/Wiles).

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL only frames the report.)

### One-line check (Phase 2b)

Body line count: ~9 substantive lines (it assembles a 4-field `ModularForm` structure: `toFun`, a multi-step `slash_action_eq'` proof via `rintro`/`rw`/`exact`, `holo'`, and a `bdd_at_cusps'` proof routed through two `IsArithmetic.isCusp_iff_isCusp_SL2Z` rewrites).
One-liner verdict: **MULTI-LINE** (kind is `def`, but the body is a non-trivial structure construction with embedded proofs, far from a one-liner).
Conclusion: MULTI-LINE — Phase 2b exemption table skipped (not a one-liner).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | `p-stabilization Eisenstein series E_k(z) − p^{k−1}E_k(pz) modular form Γ₀(p)` | **yes** | `E_k^{(p)}(z) := E_k(z) − p^{k−1}E_k(pz)` | Direct verbatim hit: "The p-stabilization of the classical Eisenstein series E_k is defined as E_k^{(p)}(z) := E_k(z) − p^{k−1}E_k(pz)". arXiv 0707.3747, 1207.0198, 2302.13009. |
| 2 | WebSearch (general form) | `p-stabilization modular form ordinary projection oldform Atkin–Lehner U_p eigenvalue definition` | **yes** | ordinary p-stabilisation selects half the Euler factor at `p`; oldform/newform via degeneracy maps stable under `U_p` | Confirms p-stabilisation is the general framework (split the level-`p` oldspace `f(z)`, `f(pz)` into `U_p`-eigenlines). Mocanu "Atkin–Lehner theory of Γ₁(N)". |
| 3 | WebSearch (named-after / aliases) | `stabilization of Eisenstein series Hida ordinary modular form V_p operator f(pz) standard` | **yes** | "For `G_k` of level one, `G_k*(z) = G_k(z) − p^{k−1}G_k(pz)` is an eigenform on Γ₀(p)" | Names it as the GL(2) **Hida/Wiles** ordinary Λ-adic Eisenstein prototype; `V_p`/`U_p` operator. Emerton (Eisenstein ideal), Franc (Hida theory notes), Dasgupta (evil Eisenstein). |
| 4 | ChatGPT MCP | (intended: "standard def + generality + historical evolution of p-stabilisation") | **n/a** | — | **ChatGPT MCP server is not installed** in this environment (only auth-required SaaS connectors are surfaced). Recorded n/a; compensated with extra WebSearch breadth (rows 1–3, 5) and arXiv (row 10), per the skill's fallback. |
| 5 | WebSearch (Iwasawa context) | `level raising operator E_k(z) − p^{k−1}E_k(pz) p-adic L-function Iwasawa` | **yes** | refinements `E − ψ(p)p^{k+1}E(p·)`, `E − τ(p)E(p·)`; Coleman families through critical-slope Eisenstein | Confirms the operator is the standard building block for p-adic L-functions of Eisenstein series. Dasgupta–Pollack–… |
| 6 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/` | **n/a** | (no references dir) | `.mathlib-quality/references/` absent and `refs/` absent in this checkout — recorded n/a (PDFs are local-only and not present here). Docstring cites "RJW TeX 2367–2394" + Miyake §4.6 + Diamond–Shurman §5.7 as the source. |
| 7 | nLab | `p-adic modular form` / `Eisenstein series` | partial | nLab has *p-adic modular form* (sections of ω^k over the ordinary locus) but no dedicated *p-stabilisation* page | The abstract p-adic-modular-form notion is present; the specific p-stabilisation operator is treated in the research literature, not nLab. |
| 8 | nCatLab (categorical) | — | **n/a** | — | Not a categorical concept; p-stabilisation is a concrete operator on a space of modular forms. No higher-categorical formulation to consult. |
| 9 | Stacks Project | — | **n/a** | — | Not an algebraic-geometry / scheme-theoretic concept in the Stacks sense (it is classical analytic/automorphic). Stacks has no modular-forms-as-functions material of this kind. |
| 9b | MathOverflow / Math.SE | `p-stabilization Eisenstein series weight k level Γ₀(p) eigenform U_p` | **yes** | Siegel–Eisenstein of level Γ₀(p) as a `U(p)`-eigenfunction with eigenvalue 1; `[p]⁺,[p]⁻` of weight 2 giving `U_p`-eigenvalues `1` and `p` | Confirms the GL(2) weight-2 boundary case (`[p]⁺`) and the general principle; the `k ≥ 3` case is the unramified/convergent analogue. |
| 10 | recent arXiv (≤5 yr) | `Siegel–Eisenstein series of level p p-adic properties` (2505.06956); `p-adic level raising eigenvariety U(3)` (2504.00821) | **yes** | active 2024–2025 work on level-`p` Eisenstein series and level-raising | Confirms it is live, standard, generalised in many directions (Siegel, unitary); the GL(2) elliptic case (this decl) is the classical prototype. |

### Literature summary (Phase 3)

Concept identified as: **the p-stabilisation (a.k.a. ordinary / p-stabilised / "evil" Eisenstein) of the level-1 Eisenstein series**, `E_k^{(p)}(z) = E_k(z) − p^{k−1}E_k(pz)`, an eigenform of weight `k` and level `Γ₀(p)`. It is one of the two `U_p`-eigenstabilisations of the level-`p` oldform `{E_k(z), E_k(pz)}` (the one with `U_p`-eigenvalue `1`; the other has eigenvalue `p^{k−1}`).
Sources agree on the standard form: **yes** — the formula `E_k(z) − p^{k−1}E_k(pz)` is verbatim across the analytic-number-theory literature (Hida, Wiles, Emerton, Dasgupta; the Siegel/unitary generalisations reduce to it for GL(2)).
Most general standard form: the **p-stabilisation / degeneracy-and-`U_p`-eigenline construction**: given a level-1 (or level-`N`, `p ∤ N`) eigenform `f`, its `V_p`-degeneracy `f(pz)` spans, together with `f`, the `p`-oldspace at level `Np`, on which `U_p` acts with characteristic polynomial `X² − a_p X + p^{k−1}`; the p-stabilisations are the `U_p`-eigenvectors. For the Eisenstein series the `a_p`/roots are explicit, giving `E_k − p^{k−1}E_k(p·)` and `E_k − E_k(p·)`.
Generality dimensions where the literature varies:
  - **modulus**: from a single prime `p` → prime-power `p^r` → general level `N` with a chosen `p ∤ N` (degeneracy at `p`). The most general elliptic-modular form is "for any tame level `N` and prime `p ∤ N`".
  - **group**: GL(2) (this decl) → Siegel Sp(2n) → unitary GU(n) (the arXiv hits). The GL(2) case is the prototype.
  - **weight**: `k ≥ 3` (absolute convergence, this decl's hypothesis) is the standard analytic range; `k = 2` is the boundary `[p]⁺` case treated separately.
Disagreement with the literature: **none** on the formula. The decl's form *is* the literature-standard GL(2) p-stabilisation. The only gap is **specialisation**: the decl fixes a single prime `p` (via `[Fact p.Prime]`) where the literature states it for a general level and a general degeneracy operator `V_d`.

---

### Generality analysis — `PadicLFunctions.stabilisedEisenstein`

Literature-standard form (from Phase 3): the p-stabilisation `f ↦ f − a·(f ∣ V_d)` as one of the `U_p`-eigenlines of the `p`-oldspace, stated for a general tame level `N`, a general degeneracy index `d` (here `d = p`), and applicable to any level-`N` eigenform `f` (here `f = E_k`).

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `(p : ℕ) [Fact p.Prime]` | a **fixed prime** baked into the def via a section variable | general modulus: any `d ≥ 1` for the `V_d` degeneracy; the level can be `Γ₀(N)` for any `N` with the prime degeneracy at any `p ∣ N` | **yes** | The underlying `levelRaiseFun d`/`levelRaiseMatrix d`/`modularFormLevelRaise M d` operators are already stated for general `d` with only `[NeZero d]` (see `LeanModularForms/HeckeRIngs/GL2/LevelRaise.lean:48,56,257`). Primality is used only to land in `Γ₀(p)` (vs `Γ₀(N)`); the construction itself does not need `p` prime. **The fixed-prime form is a specialisation.** |
| 2 | `{k : ℕ} (hk : 3 ≤ k)` | weight `k ≥ 3` | `k ≥ 3` (convergence) is the standard analytic range; `k ≥ 4` even for the q-expansion bridge | NO (for this object) | `3 ≤ k` is exactly mathlib's `ModularForm.E` hypothesis (`EisensteinSeries/Basic.lean:47`). This is the maximally-general convergent range; not a weakening target. |
| 3 | input form `= ModularForm.E hk` (hard-wired) | the construction is hard-wired to *the* Eisenstein series | p-stabilisation is an operator `f ↦ f − a_p·(f∣V_p)` definable on **any** modular/cusp form for the level | **yes** | Mathematically the p-stabilisation is a *function of an arbitrary form* `f`; specialising the input to `E_k` at definition time is the narrow form. The modern-idiom target (4c) is to expose the **operator** `modularFormPStabilise` and obtain `stabilisedEisenstein` as `pStabilise (E_k)`. |
| 4 | level group `(Gamma0 p).map (mapGL ℝ)` | image of `Γ₀(p) ≤ SL₂(ℤ)` under `mapGL ℝ` into `GL₂(ℝ)` | the same; this is the correct mathlib-idiomatic ambient group for modular forms (`ModularForm 𝒢 k` over `𝒢 ≤ GL₂(ℝ)`) | NO | The `(·).map (mapGL ℝ)` packaging matches mathlib's `ModularForm` convention (forms live over `Subgroup (GL (Fin 2) ℝ)`); correct as-is. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD**
Number of weakening opportunities found: **2 substantive** (rows 1 and 3): (a) fixed prime `p` → general modulus/level, (b) hard-wired `E_k` input → an Eisenstein/`U_p`-eigenline of a general form.
Proposed restatement (literature-weakening target):

```lean
-- the degeneracy/p-stabilisation OPERATOR for a general modulus d, then E specialises:
noncomputable def modularFormPStabilise (N d : ℕ) [NeZero d] (k : ℤ)
    (f : ModularForm (Γ₀(N).map (mapGL ℝ)) k) (a : ℂ) :
    ModularForm (Γ₀(N*d).map (mapGL ℝ)) k := …      -- f − a • (levelRaise of f)
-- and then:
noncomputable def stabilisedEisenstein' {k : ℕ} (hk : 3 ≤ k) (p : ℕ) [NeZero p] :
    ModularForm ((Γ₀(p)).map (mapGL ℝ)) (k : ℤ) :=
  modularFormPStabilise 1 p k ((ModularForm.E hk).restrictSubgroup …) ((p:ℂ)^(k-1))
```

Cost of restatement: **MODERATE** — the building blocks (`modularFormLevelRaise` for general `d`, `restrictSubgroup`, the Γ₀-conjugation bridge) already exist *for general `d`* in `LeanModularForms`; assembling the general operator + re-deriving the slash-invariance for `Γ₀(N)` instead of `Γ₀(p)` is mechanical-to-moderate, not a new-ideas problem. **Cost does not downgrade the verdict (mathlib values the right form).**

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|---------------------------------|
| 1 | "let X be a foo" preambles → typeclasses/instances? | partial-no | `[Fact p.Prime]` is already a typeclass; the issue is that `p` is *fixed* (Phase 4a row 1), not that it's a hypothesis-vs-instance question | n/a |
| 2 | sequences/metric → filters/topological? | **no** | — | No sequential/metric content; this is an algebraic operator on a function space. |
| 3 | construct an object where a **universal-property / operator class** would characterise it? | **yes** | Expose the p-stabilisation as an **operator** `f ↦ f − a·(f∣V_p)` (i.e. `modularFormPStabilise`), with `stabilisedEisenstein = pStabilise (E_k)` a one-line specialisation. The operator is the genuinely reusable object; the Eisenstein instance is a corollary. | Every other p-stabilisation in mathlib (of cusp forms, of `Δ`, of newforms) would reuse the one operator; the `U_p`-eigenvalue lemmas (`U_p (pStabilise f) = …`) attach once, to the operator, not per-form. |
| 4 | set-with-closure-predicate → bundled substructure? | **no** | — | No subset/closure structure here. |
| 5 | vector-space/metric/field-specific → weaker typeclass? | **no** | — | Already over the right objects (`ℂ`-valued modular forms over a `GL₂(ℝ)` subgroup). |
| 6 | 1-categorical → higher-categorical? | **no** | — | Not categorical. |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group? | **partial** | The degeneration index `p` should be a general `d ≥ 1` (matches Phase 4a row 1; the operator `V_d` is the natural general index) | unifies with the general `levelRaise M d` already in the project; lets `U_p ∘ U_q` composition lemmas exist. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes**
  - Proposed mathlib-idiomatic restatement: factor out the **p-stabilisation / degeneracy operator** `modularFormPStabilise` (general modulus `d`, general input form `f`, general level `N`), and define `stabilisedEisenstein` as the specialisation `pStabilise (E_k)`. This is the same target as Phase 4b's literature-weakening, reached from the operator-abstraction direction.
  - Cost: **MODERATE** (the general-`d` level-raise operator already exists in the project).
  - Mathlib downstream this enables: (i) one `U_p`-eigenvalue API attached to the operator instead of re-proved per form; (ii) reuse for p-stabilisations of cusp forms / newforms (the entire ordinary-projection and Hida-family machinery the project is heading toward); (iii) `V_p ∘ V_q` / degeneracy-composition lemmas; (iv) the q-expansion law `aₙ(pStabilise f) = aₙ(f) − a·a_{n/p}(f)` stated once.
  - Real mathematical improvement (not just "looks cooler"): the **operator** is the object the literature actually reuses (oldform theory, ordinary projection, `U_p`-eigenlines, p-adic families); shipping the Eisenstein specialisation without the operator would force every future p-stabilisation to re-derive the same level-raising-and-subtract construction.

---

### Diamond / defeq risk — `PadicLFunctions.stabilisedEisenstein` (Phase 4.5; kind = `def`)

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | **none** | The def *produces* a `ModularForm` term; it introduces no new instance and no new typeclass. The only instance in play is `NeZero p` derived locally from `[Fact p.Prime]` (a `haveI`, scoped to the body), which cannot collide with anything outside. |
| 2 | Reducibility leak | **none** | Plain `noncomputable def`, not `@[reducible]`/`abbrev`. The body (a `ModularForm` structure literal) is sealed; nothing forces it open to defeq-checking. The companion `coe_stabilisedDiff`/`stabilisedEisenstein_apply` lemmas (the latter proved with `change … ; rw; simp`) are the intended unfolding API. |
| 3 | Non-canonical unfolding | **low** | `stabilisedEisenstein_apply` rewrites to the pointwise formula via `coe_stabilisedDiff` + `simp only [Pi.sub_apply, …]`; `rfl`-unfolding of the structure to `stabilisedDiff` works (it is defeq), which is intended and matches `coe_stabilisedDiff := by rfl`. No surprising `simp` behaviour — there is no `@[simp]` on the def. |
| 4 | Instance priority collision | **n/a** | Not an `instance`. |
| 5 | Universe-polymorphism issues | **none** | Everything is at `Type` (modular forms of ℂ-valued functions on `ℍ`); no universe variables, no polymorphic call sites to break. |
| 6 | Coercion ambiguity | **low** | The `ModularForm`→`(ℍ → ℂ)` `FunLike` coercion is mathlib's existing one (used as `stabilisedEisenstein p hk z` in `_apply`); the def adds no new `CoeFun`/`CoeSort`. No competing coercion path. |

### Risk verdict (Phase 4.5)

Overall risk: **NONE/LOW** (no row is HIGH). It is a sealed `noncomputable def` returning an existing structure type with no new instances/coercions/universes.
Top risks: none.
Recommended mitigations: none required. (Keep `coe_stabilisedDiff` + `stabilisedEisenstein_apply` as the unfolding API; do not mark the def `@[simp]` or `@[reducible]` — both already respected.)

---

### Mathlib search-status: `PadicLFunctions.stabilisedEisenstein`

```
[A] Lean-Finder       p-stabilisation Eisenstein / Gamma0 modular form        n/a — endpoint unavailable (HTTP 405/404 from leansearch.net)
[B] Loogle            ModularForm (CongruenceSubgroup.Gamma0 _) _              0 results
                      "Eisenstein" (full name search)                         hits, but only level-1 / 𝒮ℒ / Gamma N — NOTHING at Gamma0 or p-stabilisation
[C] LeanSearch        "p-stabilised Eisenstein series modular form Gamma0"     n/a — endpoint returned HTTP errors (404/405); concept resolved by [B]+[D]+lit
[D] Grep mathlib src  stabilis(ed|ation) ∩ {eisenstein,modular}               no hits (only Order/Noetherian/ContinuedFractions "stabilise", unrelated)
                      oldform | atkin | lehner | "p-stabil" | U_p             no hits
                      restrictSubgroup                                        no hits (project-only, in LeanModularForms)
                      levelRaise | level_raise | modularFormLevelRaise        no hits (project-only)
                      ModularForm (Gamma0 …) / Eisenstein at Gamma0 level      no hits — mathlib's Eisenstein API stops at ModularForm.E (𝒮ℒ) and eisensteinSeriesMF (Gamma N)
[E] Name pattern      grep def/theorem .*[Ss]tabilis.*{eisenstein,modular}     no hits
```

Searched for both:
  - the user's current form (fixed-prime Γ₀(p) p-stabilised Eisenstein) — **not in mathlib**;
  - the literature-standard general form (a `V_d`/p-stabilisation operator, an Eisenstein form at any `Γ₀(N)`, a level-raising operator) — **also not in mathlib**. Mathlib has `ModularForm 𝒢 k` for general `𝒢 ≤ GL₂(ℝ)`, `CongruenceSubgroup.Gamma0/Gamma1`, `IsArithmetic`, and the level-1 `ModularForm.E` / `Gamma N` `eisensteinSeriesMF`, but **no** Γ₀-level Eisenstein form, **no** `restrictSubgroup` for forms, and **no** level-raising / `V_p` operator.

Concluded: **not in mathlib** (Loogle + two grep families + name-pattern all exhausted, under both the user's form and the general literature form; LeanSearch/Lean-Finder endpoints unavailable but the concept-level negative is decisive from the other methods + the literature). Both the object **and its entire supporting stack** (`modularFormLevelRaise`, `restrictSubgroup`, the `mapGL`/`Gamma0` Eisenstein image API) are absent from mathlib and currently live only in the sibling `LeanModularForms` project.

---

### Call sites — `PadicLFunctions.stabilisedEisenstein` (Phase 6.0)

Internal use count: **0** outside the declaring file (no other project `.lean` file references it).
External-to-file callers: **0 files** (grep over `projects/**/*.lean` minus `.lake` returns only `EisensteinComplex.lean`).

Within the declaring file (context — these are the *consumers* that make it a live main-result construction, not dead code):

| Caller (same file) | Usage pattern |
|--------------------|---------------|
| `EisensteinComplex.lean:352` (`stabilisedEisenstein_apply`) | `stabilisedEisenstein p hk z = ModularForm.E hk z − (p:ℂ)^(k-1) * ModularForm.E hk (pScale p z)` — the pointwise formula |
| `EisensteinComplex.lean:365` (`stabilisedEisenstein_smul_apply`) | `((zetaNeg (k-1):ℂ)/2) * stabilisedEisenstein p hk z = rjwEisenstein … − p^{k-1}·rjwEisenstein …(pScale)` — the bridge to `rjwEisenstein`, whose q-expansion is the file's headline result `hasSum_stabilisedEisenstein` (line 187) |

Inline-derivation grep (was the same object re-derived elsewhere without using `stabilisedEisenstein`?): **(none)** — `pScale` and the `E − p^{k−1}E(p·)` combination appear nowhere outside this file.

What the pattern tells us: K = 0 *external* uses, but this is **not** the "dead wrapper consumers bypass" case. The def is brand-new and is the *named target object* of its own file (docstring "Main": `see stabilisedEisenstein`); its two same-file consumer theorems plus the q-expansion `hasSum_stabilisedEisenstein` are the deliverables. Per the Phase 6 table this is "genuinely new + few current consumers" — a YES-leaning signal qualified by "the consumer base is the project's own forthcoming p-adic L-function machinery, which is mid-development."

### Composition check (Phase 6)

Can `stabilisedEisenstein` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: `(ModularForm.E hk).restrictSubgroup … − c • modularFormLevelRaise 1 p k (…)` (this is literally `stabilisedDiff`, then promote the slash-invariance from Γ₁(p·1) to Γ₀(p)).
  - Mathlib decls used: `ModularForm.E` only. `restrictSubgroup`, `modularFormLevelRaise`, and the Γ₀-promotion (`stabilisedDiff_slash_mapGL`, `slash_mapGL_levelRaiseFun`, `levelRaiseConjOfDvd_mem_Gamma0`, `IsArithmetic.isCusp_iff_isCusp_SL2Z`) are **all project-local (LeanModularForms), not mathlib**.
  - Result: **fails** as a *mathlib* composition. It needs an entire non-mathlib operator stack plus a genuine slash-invariance proof (the `stabilisedDiff_slash_mapGL` argument is multi-step: `sub_eq_add_neg`, `SlashAction.add_slash`, the down-conjugation bridge, two `E_slash_mapGL` applications).
  - Notes: the `bdd_at_cusps'` field alone routes through two `IsArithmetic.isCusp_iff_isCusp_SL2Z` rewrites — not a 1–3-call glue.

Attempt 2 (any mathlib-only angle): none exists — mathlib has no Γ₀-Eisenstein form and no level-raising operator to compose from (Phase 5).

Conclusion: **NOT-COMPOSABLE** (from mathlib). It is a real construction requiring an operator stack and a slash-invariance proof, both currently outside mathlib; far more than 3 mathlib calls and involves genuine reasoning, not glue.

---

## Verdict: `PadicLFunctions.stabilisedEisenstein`

**Category:** `YES-but-generalise-first`

**Evidence:**
- Literature search (Phase 3): the formula `E_k(z) − p^{k−1}E_k(pz)` is the **verbatim, classically-named** p-stabilisation (Hida/Wiles ordinary Λ-adic Eisenstein prototype for GL(2)); ≥6 channels hit, sources agree on the form, and they state it more generally (general level `N`, general degeneracy `V_d`, as one `U_p`-eigenline of the `p`-oldspace).
- Generality analysis (Phase 4b): **STRICTLY NARROWER THAN STANDARD** — the def fixes a single prime `p` and hard-wires the input `E_k`, whereas the standard form is an operator `f ↦ f − a·(f∣V_d)` for general modulus and general input.
- Modern-idiom (Phase 4c): **yes** — factor out the p-stabilisation/degeneracy **operator** (`modularFormPStabilise`), with `stabilisedEisenstein = pStabilise (E_k)`; the operator is what the literature reuses (oldform theory, `U_p`-eigenlines, ordinary projection, Hida families).
- Diamond/defeq risk (Phase 4.5): **NONE/LOW** (sealed `noncomputable def`, no new instances/coercions/universes).
- Mathlib search (Phase 5): **not in mathlib**, under both the user's form and the general form — and **neither is its supporting stack** (`modularFormLevelRaise`, `restrictSubgroup`, Γ₀-Eisenstein image API), which lives only in `LeanModularForms`.
- Composition check (Phase 6): **NOT-COMPOSABLE** from mathlib (needs a non-mathlib operator stack + a genuine multi-step slash-invariance proof).

**Rationale.**
The content unambiguously belongs in mathlib: the p-stabilised Eisenstein series is a standard, named object at the foundation of p-adic L-functions and Hida theory, mathlib's Eisenstein API currently dead-ends at level 1 (`ModularForm.E`) / `Gamma N` (`eisensteinSeriesMF`) with nothing at `Γ₀`, and the construction is a genuine multi-field modular-form assembly (not a one-liner, not a ≤3-call composition). That rules out both NO buckets and the one-liner trap. So the only question is YES-add-as-is vs YES-but-generalise-first — and two independent signals push to the latter. (1) **Literature-weakening:** the decl fixes a single prime `p` via `[Fact p.Prime]` and hard-wires `E_k`, but the standard form is the degeneracy/`U_p`-eigenline construction for a general level and a general degeneration index `V_d`; the underlying `levelRaiseFun d`/`modularFormLevelRaise M d` operators are *already* stated for general `d` in the project, so the fixed-prime form is a strict specialisation (Phase 4b). (2) **Modern-idiom (Bourbaki 2.0):** the reusable object is the **operator** `f ↦ f − a·(f∣V_p)`, with the Eisenstein form a one-line corollary — shipping only the Eisenstein specialisation would force every future p-stabilisation (cusp forms, newforms, the ordinary projector) to re-derive the same level-raise-and-subtract, and would scatter the `U_p`-eigenvalue / q-expansion API across forms instead of attaching it once to the operator (Phase 4c downstream list).

There is also a hard **prerequisite** that reinforces "generalise first": the decl's entire dependency stack — `modularFormLevelRaise`, `CuspForm/ModularForm.restrictSubgroup`, and the `Γ₀(p).map (mapGL ℝ)` Eisenstein-image API — is **not in mathlib** (Phase 5); it lives in the sibling `LeanModularForms` project. So this object cannot be PR'd to mathlib in isolation regardless of generality: the level-raising operator and `restrictSubgroup` must be upstreamed first (themselves excellent mathlib candidates), and at that point the natural thing to upstream alongside them is the *general* p-stabilisation operator, with `stabilisedEisenstein` as its Eisenstein instance — exactly the YES-but-generalise-first target. The generalisation cost is MODERATE (the general-`d` machinery already exists in-project), and per the skill cost never downgrades the verdict.

**Refactor-actionable / upstreaming plan.**

Reason for the generalisation: **both** —
  - LITERATURE-WEAKENING: Phase 4b found the fixed-prime, hard-wired-`E_k` form strictly narrower than the literature-standard general-modulus degeneracy/`U_p`-eigenline construction.
  - MODERN-IDIOM (Bourbaki 2.0): Phase 4c found the contemporary mathlib formulation is the **operator** `modularFormPStabilise`, a real organisational improvement.

Proposed restatement:

```lean
/-- The level-raising / V_d degeneracy operator already exists in-project for general `d`;
    expose the p-stabilisation operator built from it. -/
noncomputable def modularFormPStabilise (N d : ℕ) [NeZero d] (k : ℤ)
    (f : ModularForm ((CongruenceSubgroup.Gamma0 N).map (mapGL ℝ)) k) (a : ℂ) :
    ModularForm ((CongruenceSubgroup.Gamma0 (N * d)).map (mapGL ℝ)) k := by
  sorry  -- f.restrictSubgroup … − a • modularFormLevelRaise N d k (f.restrictSubgroup …);
         -- slash-invariance generalises stabilisedDiff_slash_mapGL from Γ₀(p) to Γ₀(N·d).

/-- The p-stabilised Eisenstein series as the Eisenstein specialisation of the operator. -/
noncomputable def stabilisedEisenstein {k : ℕ} (hk : 3 ≤ k) (p : ℕ) [NeZero p] :
    ModularForm ((CongruenceSubgroup.Gamma0 p).map (mapGL ℝ)) (k : ℤ) :=
  modularFormPStabilise 1 p (k : ℤ)
    ((ModularForm.E hk).restrictSubgroup …) ((p : ℂ) ^ (k - 1))
```

Estimated cost of regeneralisation: **MODERATE** (general-`d` level-raise + `restrictSubgroup` already in `LeanModularForms`; the only new work is stating the operator over `Γ₀(N·d)` and re-running the slash-invariance argument for general `N` instead of the `N = 1`, prime-`p` case). EXPENSIVE-free; and cost does not downgrade the verdict.

Mathlib downstream this enables (MODERN-IDIOM, required):
  - one `U_p`-eigenvalue lemma (`U_p (modularFormPStabilise … a) = …`) and one q-expansion law (`aₙ = aₙ(f) − a·a_{n/d}(f)`) attached to the operator, reused by every form;
  - reuse for p-stabilisations of cusp forms / newforms — the ordinary-projection and Hida-family machinery the project is building toward;
  - `V_d` degeneracy-composition lemmas (`V_d ∘ V_e`), blocked by the hard-wired single-prime form;
  - fills the concrete mathlib gap: mathlib's modular-forms API has level-1 (`ModularForm.E`) and `Gamma N` (`eisensteinSeriesMF`) Eisenstein series but **nothing at `Γ₀`** and **no level-raising/degeneracy operator at all** — this is the missing `Γ₀`/`V_p` layer.

Prerequisite (upstream first — these gate the PR and are themselves strong mathlib candidates):
  1. `ModularForm.restrictSubgroup` / `CuspForm.restrictSubgroup` (restriction along `Γ' ≤ Γ`) — `LeanModularForms/HeckeRIngs/GL2/LevelRaise.lean`.
  2. `levelRaiseMatrix` / `levelRaiseFun` / `modularFormLevelRaise` (Miyake §4.6 Lem 4.6.1, general `d`) — same file.
  3. the `Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z` cusp-transfer and the `mapGL`/`Γ₀` modular-form-image plumbing.

Next action: run `/generalise PadicLFunctions.stabilisedEisenstein` (it will tension against both the literature-standard general-modulus form from Phase 3 and the operator form from Phase 4c) to produce `modularFormPStabilise`; **before any mathlib PR**, upstream the prerequisite level-raising / `restrictSubgroup` stack from `LeanModularForms` (each its own `feat(NumberTheory/ModularForms): …` PR), then ship the general p-stabilisation operator with `stabilisedEisenstein` as its Eisenstein instance. PR grouping: ship `modularFormPStabilise` + `stabilisedEisenstein` + `stabilisedEisenstein_apply` (and the q-expansion `hasSum_stabilisedEisenstein`) as one coherent "p-stabilised Eisenstein series" PR, on top of the level-raising-operator PR.

---

## Next step

Run `/generalise PadicLFunctions.stabilisedEisenstein` to restate it via a general p-stabilisation/degeneracy operator `modularFormPStabilise` (general modulus, general input form), tensioning against both the literature-standard form and the modern operator idiom. In parallel, upstream the prerequisite level-raising operator + `restrictSubgroup` + `Γ₀`-image API from `LeanModularForms` to mathlib (they are absent there and are prerequisites for any PR of this object); then ship the general operator with `stabilisedEisenstein` as its Eisenstein specialisation as one PR.
