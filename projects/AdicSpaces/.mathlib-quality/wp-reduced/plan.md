# Development Plan: WP — the rationally stably reduced example (§6)

**Branch**: `wp/reduced-example` (off `fjp/cdvf-lemma51` @ b007a4f3d).
**Worktree**: `/Users/mcu22seu/Documents/GitHub/aintlib-adic-fjp`.
**Source**: `refs/AdicSpaces/uniform_sheafy_domains_with_reduced_example.tex` §6 (655–1318).
**Prose extraction** (binding Step-1 artifact): `wp-reduced/paper-extraction.md`.

## Goal

Formalise Theorem `thm:rationally-reduced-example`: the weighted-parity algebra 𝒜 over a
CDVF base K is (1) a complete uniform Tate integral domain, nonnoetherian, with 𝒜° = 𝒜₀;
(2) strongly sheafy; (3) rationally stably reduced; (4) has the genuine rational chart
ℬ = 𝒜⟨W/ϖ⟩ an integral domain but not uniform — hence 𝒜 is uniform, sheafy, not stably
uniform, with a REDUCED bad chart (contrast with the FJP example, whose bad chart has a
nilpotent).

Endpoint staging (binding): endpoints (1),(2),(4) are deliverable independently of (3);
within (3), the descent mechanism is deliverable independently of the head-reducedness
input HRW (the one classical wall), which is quarantined behind a single Prop-valued
hypothesis until its own sub-campaign discharges it.

## Base-field conventions (identical to FJP-CDVF)

`variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]`
with `FiniteJetOver.Uniformizer K` (explicit ϖ layer) and the `[IsDiscreteValuationRing 𝒪[K]]`
layer providing `Uniformizer.ofDVR`. Norm-multiplicativity of K is available
(NontriviallyNormedField). Discreteness enters where the paper's "attains its norm" /
"scale to norm one" arguments run — thread through `Uniformizer` exactly as FJP did.

## Core design decisions

### D1. Variable index and ambient ring
σ := ℕ, with `0` playing W and `n+1` playing U_{n+1} (paper's U_n, n ≥ 1). Ambient:
`MvPowerSeries.Restricted K (fun _ : ℕ => (1:ℝ))` (vendored Coram; NormedRing via
gaussNorm, IsUltrametricDist; LinearOrder ℕ feeds the absolute-value/multiplicativity
layer). GAP to fill: `CompleteSpace` for infinite σ (adapt the univariate
`Restricted.isCompleteSpace`; general σ statement, reusable).

### D2. Parity weight on Finsupp exponents
For `t : ℕ →₀ ℕ`: `wpWeight t := ∑ n ∈ t.support.filter (fun n => 1 ≤ n ∧ Odd (t n)), n`
— formalised as a sum over the support; equivalently via `Finsupp` filter. API: value on
single/add of disjoint supports (additivity), subadditivity (parity case analysis),
`wpWeight (2•t) = 0`-type evenness lemmas. Support predicate:
`WPMem t : Prop := wpWeight (tail t) ≤ t 0` where `tail t` zeroes index 0. Monoid:
`WPMem s → WPMem t → WPMem (s+t)` (subadditivity + t 0 additive).

### D3. 𝒜 as closed support subalgebra (rem:formalization convention)
`wpSupport K : Subalgebra K (Restricted K 1)` := series with all coefficients supported on
`WPMem`. `WPA K := ↥(wpSupport K)`. Closedness of the support condition ⇒ CompleteSpace;
NormedRing by restriction; unit ball `wpUnitBall = 𝒜₀`; IsTateRing/IsHuberRing instance
stack copied from the FJP JetA pattern. (Membership is a coefficientwise ∀-condition;
products stay supported because the complement of a monoid ideal… precisely: WPMem is
add-closed and MvPowerSeries.coeff_mul sums over antidiagonal pairs.)

### D4. Heads as support subalgebras; free normal form; NO quotient presentation
`wpHead N ⊆ wpSupport` := additionally `t.support ⊆ {0} ∪ [1,N]` (no variable index > N).
`WPHead K N := ↥…`. Documented route change vs the paper's quotient presentation
(paper-extraction §6.1): the load-bearing content is the unique factorization
eq:parity-factorization giving `WPHead K N` = FREE module of rank 2^N over the Tate
subalgebra T_N = K⟨W, U_1²,…,U_N²⟩-analogue, basis Y^ε = ∏ (W^n U_n)^{ε_n}. Consequences
proven directly on the support side: `IsNoetherianRing (WPHead K N)` (via
`IsNoetherianRing.of_finite` over T_N ≅ P K (N+1)-image), noetherian unit ball,
`IsStronglyNoetherian (WPHead K N)` (same free decomposition after adjoining Tate
variables), `IsSheafyComplete`/`IsSheafyFor` via `isSheafyFor_of_stronglyNoetherianTate`,
domain (restricted Gauss multiplicativity), density of ⋃_N heads in 𝒜.
B2-log guard: strong noetherianity is NEVER inferred from noetherianity (prior B2
T-SUM-6/T-Q4: that implication is false); it is proven for every Tate-variable count k by
the same finite-free-module argument at head K⟨W,Z,T₁…T_k⟩.

### D5. Tail decomposition WITHOUT abstract c₀-module theory
Tail indices: `μ : ℕ →₀ ℕ` with support ⊆ (N,∞). Monomial-level split
S ≅ S_N × Tails (disjoint-support additivity of wpWeight). Lean carries this as
COEFFICIENT-REGROUPING API on 𝒜 (no bundled ⊕̂^{c₀} object): for f : WPA and tail μ, the
head coefficient `tailCoeff N μ f : WPHead K N` with (i) norm lemmas
`‖tailCoeff N μ f‖ ≤ ‖f‖`, `‖f‖ = ⨆ μ ‖tailCoeff N μ f‖`; (ii) null-family lemma; (iii)
reconstruction `f = ∑' μ, e_μ • tailCoeff…` as needed (or characterized coefficientwise
to avoid tsum); (iv) `tailCoeff` of a product = twisted convolution (eq:tail-multiplication
with W^{excess} factors); (v) ρ_N := tailCoeff N 0 is a norm-nonincreasing ALGEBRA
retraction onto the head (tail-content monomials form a monoid ideal). The "c₀-sum"
of the paper is then: a general gadget `WPTailFamily P := {x : Tails → P // null family}`
only where genuinely needed (the localization comparison), with pointwise ops and the
twisted product — defined ONCE, parametric in a normed algebra P with a distinguished
"W-image" element (needed for the twist) — this is `TwistedC0 (P) (wElem)`.

### D6. Rational localization interface
All identifications with the paper's completed localizations go through the project's
`RationalLocData` + `presheafValue` (B2 #25 guard: presheafValue is the COMPLETION of the
localization; never the naive algebraic localization). The chart follows FJP
`Over/Chart.lean` (chartDatum for (W;ϖ), rescale machinery); the coefficientwise
localization theorem produces `presheafValue (𝒜, α_N-datum) ≃ continuous-alg
TwistedC0 (presheafValue (WPHead K N, α)) …` via: closed graph ideal over 𝒜 (c₀ bounded
lifts from head Koszul `exists_d1_lift_pow`), the graph model at the head (828b machinery),
and the completion universal property.

### D7. Strong sheafiness by s-parametrization
The construction is parametrized from the start by `s : ℕ` auxiliary FREE variables:
σ_s := ℕ ⊕ Fin s (LinearOrder via Sum.Lex... decide: simpler σ_s := ℕ with variables
shifted?? NO — keep `ℕ ⊕ Fin s`, providing the order instance; or reindex σ_s ≃ ℕ and
transport — decide at skeleton time with the Coram API in view). Support condition reads
only the ℕ-part: `WPMemS s t := wpWeight (tail (t ∘ inl)) ≤ t (inl 0)`. `WPA' K s`,
heads `WPHead' K s N` := ℕ-part support ≤ N, NO constraint on Fin s exponents — heads are
then T_N-free of the same rank ⊗ K⟨V₁…V_s⟩, still strongly noetherian. All of D2–D6 run
uniformly in s; endpoint (2) instantiates s = 0; strong sheafiness = ∀ s + a bridge lemma
identifying `WPA' K s` with the project's Tate-extension `A⟨V₁…V_s⟩-model of WPA K`
(nested-vs-flat plumbing, its own ticket).
DECISION DEFERRED-TO-SKELETON (with default): if the s-generalization makes the Coram
instance layer fight (LinearOrder/StrongPos on Sum, completeness transport), fall back to:
develop everything at s = 0 and add a SEPARATE thin layer for s > 0 by transporting along
the support-preserving reindexing σ_s ≃ ℕ (an order iso exists: interleave). The math is
identical; only the bookkeeping differs.

### D8. Reducedness architecture (endpoint 3)
- `lem:formal-series-reduced` — target statement: `[CommRing P] [IsReduced P] →
  IsReduced (MvPowerSeries J P)` for arbitrary J. Proof (verified composable):
  P ↪ ∏_{𝔭 ∈ primes} P/𝔭 (kernel = nilradical = 0 by `nilradical_eq_sInf`,
  `nilradical_eq_zero`), MvPowerSeries functorial injectivity, coefficientwise iso
  `MvPowerSeries J (∏ᵢ Rᵢ) ≃+* ∏ᵢ MvPowerSeries J Rᵢ`, mathlib
  `NoZeroDivisors (MvPowerSeries σ R)` (ARBITRARY σ — verified present), products of
  reduced are reduced, `isReduced_of_injective`. All-mathlib except two small
  constructions (the product iso; the ∏ P/𝔭 embedding).
- Φ-embedding: `wpPhi : E →+* MvPowerSeries Tails P`, x ↦ (μ ↦ W^{ω(μ)}·x_μ) — ring hom
  by the twist-absorption identity; injective given W-regular on P.
- W-regularity of P = presheafValue(head, α): via `prop_8_30_flat_clean_proof`
  (Wedhorn 8.30 flatness over strongly noetherian heads) + flatness preserves
  injectivity of ·W (`Module.Flat` lTensor) + W is a nonzerodivisor in the head (domain).
- **HRW (the wall)**: `IsReduced (presheafValue (WPHead K N) α)` for every rational α.
  Quarantined: endpoint (3) is first proven CONDITIONALLY on
  `HeadLocalizationsReduced K : Prop` (∀ N α, IsReduced (presheafValue …)); the
  unconditional endpoint discharges the hypothesis from HRW's own sub-campaign
  (see decomposition.md § HRW: candidate routes — Serre/flat-CI, char ≠ 2 generic
  étaleness, classical BGR 6.2.4/1+7.3.2/10; ChatGPT consult mandated before HRW
  tickets are opened).
- Iterated localizations: the induction invariant is the finite-head class (see
  paper-extraction §6.6 design note); concrete route fixed after recon of the project's
  transitivity infrastructure.

## Mathlib inventory (verified so far; recon reports pending for project-side)

| Concept | Status | Action |
|---|---|---|
| `MvPowerSeries.Restricted R c`, gaussNorm, NormedRing, arbitrary σ | vendored (Coram) | USE |
| CompleteSpace of Restricted, infinite σ | ABSENT (only Fin n) | DEVELOP (general σ) |
| Gauss multiplicativity `isAbsoluteValue` | vendored ~CoramMvRestrictedNorm:271 | USE (check hyps) |
| `NoZeroDivisors (MvPowerSeries σ R)`, any σ | mathlib (NoZeroDivisors.lean:141) | USE |
| `IsNoetherianRing.of_finite` | mathlib | USE (heads) |
| `isReduced_of_injective` | mathlib (Nilpotent/Defs) | USE |
| `nilradical_eq_sInf`, `nilradical_eq_zero` | mathlib (Nilpotent/Lemmas:54,66) | USE |
| `IsReduced (MvPowerSeries σ P)` over reduced P | ABSENT | DEVELOP (D8 route) |
| `MvPowerSeries J (∏ Rᵢ) ≃+* ∏ MvPowerSeries J Rᵢ` | ABSENT (expected) | DEVELOP (small) |
| Wedhorn 8.30 flatness | project `prop_8_30_flat_clean_proof` | USE |
| Wedhorn 8.28(b) | project `isSheafyFor_of_stronglyNoetherianTate` | USE (heads) |
| Koszul deg-0 bounded lifts | project `exists_d1_lift_pow` etc. | USE |
| Small perturbation lemma | ABSENT everywhere | DEVELOP (general Tate) |
| presheafValue/RationalLocData interface | project | USE (recon pending) |
| IsUniform/IsStablyUniform + chart pattern | project (FJP Over/Chart) | USE as template |

## File structure (under `projects/AdicSpaces/Adic spaces/WP/`)

1. `ParityWeight.lean` — D2 combinatorics (wpWeight, subadditivity, disjoint additivity,
   parity split, WPMem monoid, head/tail exponent splitting). No topology.
2. `RestrictedComplete.lean` — infinite-σ CompleteSpace for `MvPowerSeries.Restricted R c`
   + closed-coefficient-condition subring machinery (general, reusable; feeds D1/D3).
3. `WPAlgebra.lean` — D3: wpSupport, WPA, instance stack (normed comm ring, complete,
   Tate/Huber, unit ball = 𝒜₀), coefficient API.
4. `WPUniformDomain.lean` — Gauss multiplicativity on 𝒜 (restrict ambient), 𝒜° = 𝒜₀,
   IsUniform, IsDomain.
5. `WPNonnoetherian.lean` — ψ_m coefficientwise, ideal chain, ¬IsNoetherianRing.
6. `WPHeads.lean` — D4: wpHead, head instances, T_N free decomposition, noetherian +
   strongly noetherian + sheafy heads, density.
7. `WPTail.lean` — D5: tailCoeff, ρ_N, twisted product rule, TwistedC0 gadget.
8. `WPPerturbation.lean` — lem:small-perturbation for a general complete Tate ring
   (project RationalLocData vocabulary), + Bezout-scaling helpers.
9. `WPCoeffLocalization.lean` — D6: closed graph ideal over 𝒜, presheafValue comparison,
   naturality, cor:finite-head-presentation.
10. `WPChart.lean` — ℬ (weighted support model), chart identification with
    presheafValue (W;ϖ), ℬ domain, ℬ nonuniform (T_n family), ¬IsStablyUniform 𝒜.
11. `WPSheafy.lean` — head Čech bounded gluing, rational-basis sheaf condition,
    IsSheafyFor/IsSheafyComplete for 𝒜 (+ s-version / strong sheafiness endpoint per D7).
12. `WPReduced.lean` — D8: MvPowerSeries reducedness, Φ, W-regularity, conditional +
    (eventually) unconditional endpoint (3); HRW sub-campaign gets its own file(s)
    `WPHeadReduced*.lean` when opened.
13. `WPMain.lean` — headline endpoints (FiniteJetMain pattern; one declaration per
    conclusion + assembly).

## Dependency graph (files)

ParityWeight → WPAlgebra → {WPUniformDomain, WPNonnoetherian, WPHeads} → WPTail
→ {WPChart, WPCoeffLocalization} ; WPPerturbation (independent of WP* until used by
WPCoeffLocalization + WPSheafy) ; WPCoeffLocalization → WPSheafy → WPMain ;
{WPTail, WPCoeffLocalization} → WPReduced → WPMain ; RestrictedComplete → WPAlgebra.
Endpoints (1): WPUniformDomain+WPNonnoetherian. (4): WPChart. (2): WPSheafy.
(3): WPReduced (+HRW). No (3)-edge into (1),(2),(4) — staging requirement satisfied.

## Generality decisions

- Base: the FJP two-layer convention (explicit `Uniformizer K` primary; `_of_dvr`
  wrappers) — maximal consistency with the delivered FJP endpoints.
- `RestrictedComplete.lean` machinery stated for arbitrary σ and radius family c with
  StrongPos (not just c = 1): the completeness proof is radius-uniform; reusable.
- Small perturbation lemma: general complete Tate ring with topologically nilpotent unit,
  project RationalLocData shape — NOT WP-specific.
- wpWeight/monoid layer: stated for the concrete parity weight (the paper's); a general
  "weight-bounded support monoid" abstraction is NOT introduced (YAGNI — one instantiation).
- MvPowerSeries reducedness + product iso: stated in mathlib generality (contribution
  candidates).

## Known open design points (to fix at skeleton time, after recon)

- O1: exact instance stack for WPA (which of NormedCommRing/NormOneClass/T2/... the
  sheafiness framework needs — copy JetA's list).
- O2: the s-parametrization mechanics (D7 fallback decision).
- O3: iterated-localization notion for endpoint (3) (project transitivity infra?).
- O4: the exact form of the head-Čech bounded-inverse extraction (OMT vs strictness
  content of 828b).
- O5: HRW route choice (post-ChatGPT).
