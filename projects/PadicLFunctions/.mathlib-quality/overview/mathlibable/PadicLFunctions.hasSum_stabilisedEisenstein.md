# `/mathlibable` report — `PadicLFunctions.hasSum_stabilisedEisenstein`

**Final verdict: `BORDERLINE-needs-human`**

The mathematics is canonical and entirely absent from mathlib (no p-stabilisation
machinery exists there at all). What makes it BORDERLINE rather than a clean
`YES-but-generalise-first` is a genuine human judgement call about *grain* and
*timing*: this `HasSum` lemma is one tightly project-bound brick (it is hard-wired
to the project-local `rjwEisenstein`, `pScale`, `stabilisedCoeff`, `sigmaP`, `zetaNeg`,
none of which are in mathlib) whose right mathlib home is a *new section* on
p-stabilisation of Eisenstein series — and whether to upstream the brick or the
whole section, and in what generality (level 1 only vs. Dirichlet character `χ`,
level `N`), is a design decision the skill should not make unilaterally.

---

### Baseline (Phase 0)

- lake build:               build NOT re-run (stale/slow per task note); **reasoned from source** — the declaration and its full dependency chain were read directly.
- decl `PadicLFunctions.hasSum_stabilisedEisenstein`:  ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/EisensteinComplex.lean:187`
- kind:                      theorem
- has sorry:                 no (proof body lines 187–280 contain no `sorry`/`admit`)
- module docstring summary:  "The q-expansion of the p-stabilised Eisenstein series (RJW §8, complex side)" — RJW's normalised `E_k` and its p-stabilisation `E_k^{(p)}(z) = E_k(z) − p^{k−1}E_k(pz)`, identifying the q-expansion coefficients with `stabilisedCoeff`.

---

### Statement (Phase 1)

`PadicLFunctions.hasSum_stabilisedEisenstein` is a theorem stating the following.

Fix a prime `p`, an even weight `k ≥ 4`, and a point `z` in the upper half-plane
`ℍ`. Let `q = e^{2πiz}`. The **p-stabilisation** of the (RJW-normalised) weight-`k`
level-1 Eisenstein series, `E_k^{(p)}(z) := E_k(z) − p^{k−1}E_k(pz)`, has the
q-expansion

  E_k^{(p)}(z) = (1 − p^{k−1})·ζ(1−k)/2  +  Σ_{n≥1} σ^p_{k−1}(n)·qⁿ,

where `σ^p_{k−1}(n) = Σ_{d∣n, p∤d} d^{k−1}` is the prime-to-`p` divisor power sum.
Packaged as a `HasSum` over `n : ℕ` (the constant term folded into the `n=0`
summand via `stabilisedCoeff`), the series `Σ_n stabilisedCoeff(p,k,n)·qⁿ` sums to
`E_k^{(p)}(z)`. This is RJW's "easy check" (TeX 2387–2393).

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the stabilising prime (project-wide `variable`).
- `k : ℕ` — the weight.
- `z : ℍ` — a point of the upper half-plane (`UpperHalfPlane`).

Hypotheses (Lean side):
- `hk : 4 ≤ k` — weight at least 4 (so `E_k` converges absolutely; `3 ≤ k` suffices for mathlib's `ModularForm.E`, but the normalisation lemma needs `B_k ≠ 0`, i.e. `k ≥ 4` even).
- `hk2 : Even k` — even weight (odd-weight level-1 Eisenstein series vanish; also fixes the sign `(−1)^{k−1} = −1` in the `ζ(1−k) = −B_k/k` normalisation).

Conclusion (math): the prime-to-`p` divisor-sum q-expansion sums to the
p-stabilised Eisenstein series `E_k(z) − p^{k−1}E_k(pz)`.

Conclusion (Lean):
```
HasSum
  (fun n : ℕ => ((stabilisedCoeff p k n : ℚ) : ℂ) * Complex.exp (2*π*I*(z:ℂ))^n)
  (rjwEisenstein (k:=k) _ z − (p:ℂ)^(k-1) * rjwEisenstein (k:=k) _ (pScale p z))
```

**Dependency chain (all PROJECT-LOCAL, none in mathlib):**
- `rjwEisenstein hk z := (ζ(1−k)/2)·ModularForm.E hk z` — RJW's normalisation of mathlib's constant-term-1 `ModularForm.E`. (`EisensteinComplex.lean:108`)
- `pScale p z := ⟨p·z, …⟩ : ℍ` — the point `p·z`. (`EisensteinComplex.lean:99`)
- `stabilisedCoeff p k n` — `(1−pᵏ⁻¹)·ζ(1−k)/2` at `n=0`, else `σ^p_{k−1}(n)`. (`EisensteinFamily.lean:357`)
- `sigmaP p k n := Σ_{d∣n, p∤d} dᵏ` — prime-to-`p` divisor power sum (RJW R8). (`EisensteinFamily.lean:62`)
- `zetaNeg k := (−1)ᵏ·B_{k+1}/(k+1)` — rational `ζ(−k)`. (`KubotaLeopoldt/ZetaValues.lean:17`)
- helper σ-identities `sigmaP_eq_of_not_dvd`, `sigmaP_add_pow_mul_sigma_div` (`EisensteinComplex.lean:47,56`); per-point base case `hasSum_rjwEisenstein` (`EisensteinComplex.lean:158`, private).

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: a named, citable object of analytic/p-adic number theory (the **p-stabilisation of an Eisenstein series**, with its standard q-expansion), and a stated main result of RJW §8 (it is the explicit "pivot between the p-adic family and the complex q-expansion" per the `stabilisedCoeff` docstring). Theorems named for / canonical in a recognised theory are BIG.

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Body line count: ~90 substantive lines (`hasSum_rjwEisenstein` base case + reindex over multiples of `p` via `Function.Injective.hasSum_iff` + the per-coefficient σ-splitting).
One-liner verdict: **n/a** — kind is `theorem`, not `def`. (The proof is a substantial multi-step argument, the opposite of a one-liner.)

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | `p-stabilization of Eisenstein series q-expansion E_k^(p)=E_k(z)−p^{k−1}E_k(pz)` | **yes** | `E_k^{(p)}(z) := E_k(z) − p^{k−1}E_k(pz)` verbatim | Kawamura (Siegel), arXiv:2010.01325, arXiv:0707.3747 — exact formula confirmed standard |
| 2 | WebSearch (general / named theory) | `ordinary p-stabilisation Eisenstein series critical slope V_p operator q-expansion` | **yes** | critical-slope ("evil") Eisenstein series; `U_p`-refinement; coeff `Σ_{d∣n,(d,N)=1} χ(d)d^{k+1}` | Chris Williams lecture notes (Warwick); Dasgupta evil-Eisenstein; the prime-to-`N` divisor sum is exactly `σ^p` |
| 3 | WebSearch (aliases / downstream) | `p-adic L-function Eisenstein series stabilization prime-to-p divisor sum constant term (1−p^{k−1}) zeta` | **yes** | const term `L(1−κ,χ)/2`, coeffs `σ_{κ−1,χ}(m)=Σχ(d)d^{κ−1}`; `(1−p^{k−1})` is the p-adjustment | Dasgupta (Duke); Bellaïche (critical p-adic L); confirms the `(1−p^{k−1})ζ(1−k)/2` constant term |
| 4 | ChatGPT MCP | (would ask: standard form, generality, historical evolution) | **n/a** | — | **ChatGPT MCP server not configured** in this environment (only auth/Asana MCP tools surfaced). Substituted with channels 1–3 + 9–10 at three generality levels per the protocol's spirit. |
| 5 | Local references | `ls projects/PadicLFunctions/.mathlib-quality/references/`; `ls refs/` | **n/a** | — | No `references/` dir and no `refs/` symlink in the checkout (RJW PDF is local-only and absent here). Recorded n/a with reason. |
| 6 | nLab | `p-stabilization / refinement of modular form` | partial | refinement = p-stabilisation (choice of `U_p`-eigenvalue root) | nLab has "p-adic modular form" / refinement language; no dedicated Eisenstein-stabilisation page, but confirms the terminology |
| 7 | nCatLab (categorical) | — | **n/a** | — | Not a categorical concept (a concrete q-expansion identity in classical modular-forms theory). |
| 8 | Stacks Project (alg geom) | — | **n/a** | — | Not an algebraic-geometry / scheme-theoretic statement. |
| 9 | MathOverflow / Math.SE | (covered via WebSearch result corpus) | **yes** | consistent `E_k − p^{k−1}E_k(p·)` and `(1−p^{k−1})` constant term across sources | The q-expansion and the level-Γ₀(p) claim are folklore-standard; no source disagrees |
| 10 | recent arXiv (last 5y) | `semi-ordinary p-stabilization Siegel Eisenstein series p-adic interpolation` | **yes** | Kawamura arXiv:1207.0198 / 2302.13009; arXiv:2406.08460 (critical Λ-adic); arXiv:1409.8155 (evil Eisenstein, Shintani) | Active modern literature; the elliptic case here is the classical special case of these |

#### Literature summary (Phase 3)

Concept identified as: the **p-stabilisation (a.k.a. p-refinement / `V_p`-stabilisation) of the weight-`k` Eisenstein series**, `E_k^{(p)}(z) = E_k(z) − p^{k−1}E_k(pz)` — a level-Γ₀(p) modular form, central to Iwasawa theory and the construction of p-adic L-functions (Serre, Mazur, Hida, Coleman, Stevens, Dasgupta).

Sources agree on the standard form: **yes** — the formula `E_k − p^{k−1}E_k(p·)`, the level Γ₀(p), the constant term `(1−p^{k−1})·ζ(1−k)/2` (`= (1−p^{k−1})L(1−k)/2`), and the prime-to-`p` divisor-sum coefficients `Σ_{d∣n, p∤d} d^{k−1}` are stated identically across Dasgupta, Williams, Bellaïche, and the Siegel literature. RJW's statement is exactly this, in mathlib's `bernoulli` normalisation.

Most general standard form: the literature states it for a **weight `k`, a Dirichlet character `χ` of conductor dividing `N`, and tame level `N`** — constant term `L(1−k, χ)/2`, `n`-th coefficient `Σ_{d∣n, (d,p)=1} χ(d)d^{k−1}` (here `V_p`-stabilisation removes the Euler factor at one prime `p ∤ N`; iterating handles all `p ∣ N`). RJW's `hasSum_stabilisedEisenstein` is the special case **`χ` trivial, `N = 1`, single prime `p`**.

Generality dimensions where the literature varies:
  - **Character `χ`:** trivial here; the literature's general form carries a Dirichlet `χ` (and the q-expansion picks up `χ(d)`).
  - **Level `N` / number of primes:** level 1 + one prime `p` here; the literature stabilises at each prime dividing a general level `N`.
  - **Eigenvalue root chosen:** the `V_p`-stabilisation here uses the unit root `1` of `X² − a_p X + p^{k−1}` (giving the "ordinary"/`Σ qⁿ Σ_{p∤d}` form); the *other* root gives the critical-slope ("evil") stabilisation. RJW uses the ordinary one; both are standard.
  - **Group:** GL₂/ℚ (elliptic) here; the literature also does Siegel (Sp_{2g}) and Bianchi — out of scope.

Disagreement with the literature: **none.** RJW's form is the textbook elliptic, trivial-character, level-1 special case, correctly normalised.

---

### Generality analysis (Phase 4)

Literature-standard form (from Phase 3): for weight `k`, Dirichlet character `χ` mod `N`, prime `p ∤ N`, the `V_p`-stabilised Eisenstein series `E_{k,χ}^{(p)}` of level `Γ₀(Np)` has q-expansion `L(1−k,χ)/2·(1−χ(p)p^{k−1}) + Σ_{n≥1} (Σ_{d∣n,(d,p)=1} χ(d)d^{k−1}) qⁿ`.

#### 4a. Generality status table

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|--------------------------------|
| 1 | (character) — none; trivial `χ` baked in | trivial character, level 1 | general Dirichlet `χ` mod `N` | **yes** (more general) | The whole construction generalises to `E_{k,χ}`; coefficients gain `χ(d)`. NOT a mechanical weakening — needs the level-`N`/character Eisenstein API, which **does not exist in mathlib** (mathlib's `EisensteinSeries.E` is level-1 trivial-character only). |
| 2 | `hk : 4 ≤ k` | weight ≥ 4 (even) | weight `k ≥ 2` (and `k ≥ 1` with `χ` non-trivial) | partly | mathlib's `ModularForm.E` needs `3 ≤ k`; the `B_k ≠ 0` normalisation forces `k ≥ 4` even. Weight 2 needs the non-holomorphic `E_2` correction — a genuinely different (harder) object. Cannot weaken cheaply. |
| 3 | `hk2 : Even k` | even weight | odd `k` allowed once `χ` is odd | no (in this trivial-`χ` setting) | Odd-weight **level-1 trivial-character** Eisenstein series are identically 0; evenness is the right hypothesis here. Only relaxes alongside introducing `χ` (axis 1). |
| 4 | one fixed prime `p` (`[Fact p.Prime]`) | single prime `p`, level 1 | stabilise at each prime of a general level `N` | yes | Iterating the `V_p`-stabilisation over primes dividing `N`. Again gated on the missing level-`N` Eisenstein API. |
| 5 | the **RJW normalisation** `rjwEisenstein := (ζ(1−k)/2)·E` | project-local rescaling of mathlib's `ModularForm.E` | the "arithmetic"/constant-term-`ζ(1−k)/2` normalisation is the literature-standard one for L-functions | — (this is already the right normalisation) | This is the correct standard normalisation; the issue is that the *object* `rjwEisenstein` is project-local, not that the normalisation is wrong. |

#### 4b. Generality verdict

The current form is: **STRICTLY NARROWER THAN STANDARD** (axes 1 and 4: trivial character, level 1, one prime).

Number of weakening opportunities found: **2 substantive** (character `χ`; general level `N` / all primes). Both are *literature-grounded* (not speculative typeclass-walking).

Proposed restatement (literature-general target):
```
-- needs a level-N / Dirichlet-character Eisenstein series API that mathlib LACKS
theorem hasSum_stabilisedEisenstein
    {N : ℕ} (χ : DirichletCharacter ℂ N) {k : ℕ} (hk : …) (p : ℕ) (hp : p.Prime) (z : ℍ) :
    HasSum (fun n => stabilisedCoeff χ p k n * q^n)
      (E_{k,χ} z − χ(p) * p^(k-1) * E_{k,χ} (p • z))
```

Cost of restatement: **EXPENSIVE** — there is no mathlib API for level-`N`,
Dirichlet-character Eisenstein series or their q-expansions; mathlib stops at the
level-1 trivial-character `EisensteinSeries.E` / `q_expansion_bernoulli`. The
general form requires building that API first (a large, multi-PR effort), then
re-proving the divisor-sum splitting with `χ`. **Per the skill, EXPENSIVE is not a
downgrade** — but here it makes the "do we generalise first or ship the level-1
brick" question a real human decision (see Phase 7).

#### 4c. Modern-idiom check (Bourbaki 2.0)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|---|----------|----------|------------------------|---------------------------------|
| 1 | "let X be a foo" → typeclasses/instances? | no | — | The hypotheses (`p.Prime`, `4≤k`, `Even k`) are already idiomatic typeclass/Prop form. |
| 2 | sequences/metric → filters/topology? | no | — | Convergence is already stated as `HasSum` (the filter-theoretic, unordered-sum API). This is *already* the modern idiom. |
| 3 | construct an object → universal-property class? | **partially** | The truly mathlib-idiomatic target is a `qExpansion`/`PowerSeries` *coefficient* statement (`(qExpansion 1 f).coeff n = …`) for a **bundled `ModularForm Γ₀(p) k`**, mirroring mathlib's own `EisensteinSeries.E_qExpansion_coeff`, rather than a bare per-point `HasSum` about an unbundled `ℍ → ℂ` function. | composes with `qExpansion`, `ModularFormClass`, `qExpansion_coeff_unique`, the cusp-function API — the whole modular-forms q-expansion ecosystem. The bundled form already exists in the project as `stabilisedEisenstein : ModularForm … k` (docstring), so the idiomatic lemma would be about *that*. |
| 4 | set+closure-predicate → bundled substructure? | no | — | n/a. |
| 5 | vector-space/field-specific → module/(semi)ring? | no | — | n/a (statement is over ℂ inherently). |
| 6 | 1-categorical → higher-categorical? | no | — | n/a. |
| 7 | concrete index (ℕ/ℤ/ℝ) → general additive/ordered structure? | no | — | The ℕ-index on the q-expansion is intrinsic (Fourier coefficients). The `p·z` scaling on `ℍ` is the standard `V_p` action; no generalisation wanted. |

Modern idiom available: **yes (mild)** — row 3.
  - Proposed mathlib-idiomatic restatement: state the result as a `qExpansion`-**coefficient** identity for the *bundled* `ModularForm ((Gamma0 p).map (mapGL ℝ)) k` p-stabilisation (the project's `stabilisedEisenstein`), matching mathlib's `EisensteinSeries.E_qExpansion_coeff` shape, instead of (or in addition to) the bare `HasSum` about `rjwEisenstein`.
  - Cost: MODERATE (the project already has the bundled `stabilisedEisenstein`; the bridge `stabilisedEisenstein_smul_apply` exists per the module docstring).
  - Mathlib downstream this enables: `qExpansion`, `ModularFormClass`, `qExpansion_coeff_unique`, cusp-function analyticity — the q-expansion API composes with the *form*, not just a function value.
  - Real mathematical improvement (not just "looks cooler"): yes — it ties the coefficients to the canonical `qExpansion` so the rest of mathlib's modular-forms API applies; the bare `HasSum` about an unbundled `ℍ → ℂ` is a weaker interface.

This modern-idiom availability + the Phase-4b STRICTLY-NARROWER finding both push the verdict away from `YES-add-as-is`. Combined with the EXPENSIVE generalisation cost (a cost-driven tradeoff the skill forbids resolving unilaterally), it lands on BORDERLINE rather than a clean `YES-but-generalise-first`.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (no definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `PadicLFunctions.hasSum_stabilisedEisenstein` (Phase 5)

Searched both the user's form (level-1, single-prime p-stabilisation) **and** the literature-standard form (level-`N`, character `χ`).

[A] Lean-Finder — n/a: server not invoked in this environment; substituted with [D]/[E] over the mathlib source tree (authoritative for "is it there").
[B] Loogle (type-pattern) — n/a: server not invoked; the type pattern `HasSum (fun n:ℕ => _ * cexp _ ^ n) _` is generic and would only re-surface mathlib's generic `hasSum_qExpansion` (found via [D]).
[C] LeanSearch (NL) — n/a: server not invoked; substituted with the Phase-3 web corpus + [D]/[E].
[D] Grep mathlib src — terms: `p.?stabili`, `stabilis(ed|ation)`, `U_p`, `V_p`, `p-refinement`, `critical slope`, `evil Eisenstein`, `oldform`, `levelRaise`, `Gamma0.*Eisenstein` → **no hits** (the only matches for the regex were the literal token "Prime"/"prime" inside unrelated `Tactic/*` files — false positives). Eisenstein files in mathlib: `EisensteinSeries/{Basic,Defs,Summable,QExpansion,UniformConvergence,MDifferentiable,IsBoundedAtImInfty}.lean` — **all level-1, trivial-character.**
[E] Name pattern — `qExpansion`/`HasSum` Eisenstein decls in mathlib: `EisensteinSeries.q_expansion_bernoulli` (`QExpansion.lean:298`), `EisensteinSeries.E_qExpansion_coeff` (`:323`), `EisensteinSeries.E_qExpansion_coeff_zero` (`:347`), generic `UpperHalfPlane.hasSum_qExpansion` (`ModularForms/QExpansion.lean:189`). **None is about a p-stabilisation.**

Building blocks mathlib **does** have:
- `EisensteinSeries.q_expansion_bernoulli {k} (hk : 3≤k) (hk2 : Even k) (z) : E hk z = 1 − (2k/B_k)·Σ' n:ℕ+, σ_{k−1}(n)·cexp(2πiz)^(n)` — the **level-1** q-expansion in the constant-term-1 normalisation.
- `ModularForm.E hk : ModularForm 𝒮ℒ k` (`Basic.lean:47`) — the level-1 normalised Eisenstein series (the object RJW rescales).
- generic q-expansion API: `UpperHalfPlane.hasSum_qExpansion`, `qExpansion_coeff_unique`, `Periodic.qParam`.
- `riemannZeta_two_mul_nat`, `bernoulli`, `ArithmeticFunction.sigma`, `summable_norm_pow_mul_geometric_of_norm_lt_one`, `Function.Injective.hasSum_iff`.

What mathlib **lacks** (the whole p-stabilisation layer):
- no p-stabilised / Γ₀(p) Eisenstein series; no `V_p`/`U_p` operator on q-expansions;
- no prime-to-`p` divisor sum `σ^p`; no `(1−p^{k−1})ζ(1−k)/2` constant term;
- no level-`N` or Dirichlet-character Eisenstein series at all.

Concluded: **not in mathlib** (all available methods exhausted, plus the literature-standard form). Mathlib has the *level-1 base case* (`q_expansion_bernoulli`, used in the proof's private base lemma `hasSum_rjwEisenstein`) but **not** the p-stabilised statement, nor its generalisation.

---

### Composition check (+ call-sites signal) (Phase 6)

#### 6.0 Call sites — `PadicLFunctions.hasSum_stabilisedEisenstein`

Internal use count: **0** (within the project, excluding the declaring file).
External-to-file callers: **0** code references. The only `grep` hits are **docstring prose mentions**, not uses:

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `EisensteinFamily.lean:356` | `(\`hasSum_stabilisedEisenstein\` in \`EisensteinComplex.lean\`).` — docstring of `stabilisedCoeff` |
| `EisensteinFamily.lean:377` | `\`hasSum_stabilisedEisenstein\` … ` — docstring of `eisensteinFamily_interpolation` |
| `EisensteinComplex.lean:363` | `… whose q-expansion is \`hasSum_stabilisedEisenstein\`.` — docstring of `stabilisedEisenstein` (same file) |

Inline-derivation grep (was the equivalent re-derived elsewhere without using it?): **none** found.

Interpretation: **K = 0, no inline re-derivation.** Per the call-sites signal table this is "brand-new + as-yet-unused" — it is the *complex-side identification* that pairs with the p-adic `eisensteinFamily_interpolation` to give RJW's main interpolation theorem; the docstrings explicitly call it the "pivot between the p-adic family and the complex q-expansion." So it is a genuine main-result brick that downstream RJW theory will consume, not dead code — but it has **no consumer yet**, which (combined with its project-bound nature) is itself part of the BORDERLINE signal: whether it is the right standalone mathlib unit depends on what it will be used for.

#### 6a. Composition attempt

Can the statement be derived from mathlib in ≤3 chained calls?

Attempt 1: `EisensteinSeries.q_expansion_bernoulli` at `z` and at `p·z`, subtract, reindex.
  - Mathlib decls used: `q_expansion_bernoulli`, `Complex.exp_nat_mul`, `Function.Injective.hasSum_iff`.
  - Result: **fails as a composition.** This is exactly what the ~90-line proof does, and it is *not* a 1–3-call composition: it requires (i) RJW's normalisation lemma `rjw_normalisation` (`ζ(1−k) = −B_k/k` for even `k`, project-local), (ii) the base `HasSum` `hasSum_rjwEisenstein` (peeling the constant term, project-local), (iii) the reindexing of the `p·z` series over multiples of `p` via `Injective.hasSum_iff` with an off-range vanishing argument, and (iv) the per-coefficient case split using the **project-local** σ-identities `sigmaP_add_pow_mul_sigma_div` (`p∣n`) and `sigmaP_eq_of_not_dvd` (`p∤n`). Multiple `have`s with real reasoning between them — a proof, not a composition.

Attempt 2: none — the target objects (`rjwEisenstein`, `stabilisedCoeff`, `sigmaP`, `pScale`) are project-local and not expressible as a short mathlib call chain.

Conclusion: **NOT-COMPOSABLE.** (Mathlib supplies the level-1 base case as one ingredient, but the p-stabilisation identity is a genuine multi-step theorem over project-local definitions.)

---

## Verdict: `PadicLFunctions.hasSum_stabilisedEisenstein`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the p-stabilisation `E_k − p^{k−1}E_k(p·)` with constant term `(1−p^{k−1})ζ(1−k)/2` and prime-to-`p` divisor-sum coefficients is **canonical** (Dasgupta, Williams, Bellaïche, Kawamura). RJW's form = the **level-1, trivial-character** special case. The general form carries a Dirichlet `χ` and a level `N`.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** (2 literature-grounded weakening axes: character `χ`, level `N`); generalisation cost **EXPENSIVE** (mathlib has no level-`N`/character Eisenstein API). Phase 4c: a mild **modern-idiom** improvement is available (state as a `qExpansion`-coefficient identity for the bundled `ModularForm Γ₀(p) k`, à la mathlib's `E_qExpansion_coeff`).
- Mathlib search (Phase 5): **not in mathlib** — mathlib stops at the level-1 `q_expansion_bernoulli` / `E_qExpansion_coeff`; no p-stabilisation, `V_p`, `σ^p`, or Γ₀(p)/character Eisenstein layer exists.
- Composition check (Phase 6): **NOT-COMPOSABLE** (a ~90-line proof over 5 project-local definitions); call sites **K = 0** (only docstring mentions) — a genuine but as-yet-unconsumed main-result brick.

**Rationale.**
The underlying mathematics unambiguously *belongs* near mathlib: the p-stabilisation of the Eisenstein series and its explicit q-expansion are textbook objects in Iwasawa theory and the construction of p-adic L-functions, and mathlib currently has nothing past the level-1 q-expansion. So this is **not** a NO verdict (mathlib doesn't have it, and it isn't a short composition). It is also **not** cleanly `YES-add-as-is`: Phase 4b found the statement strictly narrower than the literature-standard `(χ, N)` form, and Phase 4c found a real (if mild) modern-idiom upgrade — both of which the verdict gate says forbid `YES-add-as-is`.

The reason it is **BORDERLINE rather than `YES-but-generalise-first`** is a cluster of judgement calls the skill is explicitly not allowed to resolve alone: (1) the generalisation to `(χ, N)` is **EXPENSIVE** and gated on a large missing mathlib API (level-`N` / Dirichlet-character Eisenstein series) — "ship the level-1 brick now vs. build the general API first" is precisely the cost-driven tradeoff the gate says must be put to the user, not self-resolved; (2) **every object in the statement is project-local** (`rjwEisenstein`, `pScale`, `stabilisedCoeff`, `sigmaP`, `zetaNeg`) — upstreaming the lemma means first deciding the *mathlib form of those definitions* (e.g. an arithmetic-normalised Eisenstein series, a `σ^p`/prime-to-`p` divisor sum, a `V_p` operator), which is a design conversation; (3) `K = 0` consumers means the right *grain* (this `HasSum` brick alone, vs. the bundled-`ModularForm` `qExpansion`-coefficient statement from Phase 4c, vs. the whole §8 p-stabilisation section) is genuinely undetermined from the evidence. The honest output is to surface these as questions.

**Refactor-actionable bar — BORDERLINE numbered questions:**

1. **Scope/grain:** Do you want to upstream *this single `HasSum` brick* (the per-point q-expansion of the level-1 p-stabilisation), or the *whole p-stabilisation section* (the bundled `ModularForm Γ₀(p) k` `stabilisedEisenstein` + its `qExpansion`-coefficient lemma + the `σ^p` divisor-sum API) as one coherent mathlib contribution? (The latter is the natural mathlib unit; the bare `HasSum` alone is an odd standalone.)

2. **Generality / cost:** Are you willing to first build the mathlib-side **level-`N` / Dirichlet-character Eisenstein series** API so the contribution can be the literature-standard `E_{k,χ}^{(p)}` form (constant term `(1−χ(p)p^{k−1})L(1−k,χ)/2`, coeffs `Σ_{d∣n,(d,p)=1}χ(d)d^{k−1}`)? Or do you prefer to ship the level-1 trivial-character special case now and generalise later? (This is the EXPENSIVE-cost tradeoff the skill cannot decide for you.)

3. **Normalisation:** For a mathlib contribution, should the Eisenstein series use mathlib's existing **constant-term-1** normalisation (`ModularForm.E`) or RJW's **arithmetic / `ζ(1−k)/2`** normalisation (`rjwEisenstein`)? The L-function literature uses the arithmetic one, but mathlib currently only has the constant-term-1 one — picking the mathlib-canonical normalisation is a design call.

4. **Idiom (Phase 4c):** Should the statement be restated as a `qExpansion`-**coefficient** identity for the bundled `ModularForm ((Gamma0 p).map (mapGL ℝ)) k` (mirroring mathlib's `EisensteinSeries.E_qExpansion_coeff`), rather than a bare per-point `HasSum` about the unbundled `rjwEisenstein`? (The project already has the bundled `stabilisedEisenstein` and the bridge `stabilisedEisenstein_smul_apply`.)

5. **Definitions:** Are the project-local `sigmaP` (prime-to-`p` divisor sum) and `pScale`/`V_p`-action themselves intended as mathlib contributions (with mathlib-style names, e.g. `ArithmeticFunction.sigmaCoprime` / a `V_p` slash operator)? Their mathlib form must be fixed before the lemma about them can be upstreamed.

**Next action:** user answers the questions; re-run `/mathlibable PadicLFunctions.hasSum_stabilisedEisenstein` to resolve the verdict. Likely outcomes:
- "Ship level-1 now, bundled form, mathlib normalisation" → flips to **`YES-but-generalise-first`** with reason MODERN-IDIOM (target = the `qExpansion`-coefficient statement for the bundled `ModularForm Γ₀(p) k`), generalisation to `(χ,N)` flagged as a follow-up PR; run `/generalise` next.
- "Build the `(χ,N)` API first" → **`YES-but-generalise-first`** with reason LITERATURE-WEAKENING, EXPENSIVE, target = `E_{k,χ}^{(p)}`.
- "This stays internal to the RJW p-adic-L-function project" → drop from mathlib consideration; keep project-local (the `rjwEisenstein`/`sigmaP` names are fine for project use).

---

## Next step

User answers the 5 numbered questions above; re-run `/mathlibable PadicLFunctions.hasSum_stabilisedEisenstein` to resolve to a YES-but-generalise-first (most likely) or project-local-only verdict. The mathematics is genuinely missing from mathlib (Phase 5) and non-trivial (Phase 6 NOT-COMPOSABLE), so the only open questions are grain, generality/cost, normalisation, idiom, and the mathlib form of the project-local definitions — all human design calls.
