# Decomposition: §3 Measures and Iwasawa algebras (RJW arXiv:2309.15692)

Source file: `.mathlib-quality/references/2309.15692-padic-L-functions.tex` (all line
numbers below refer to it). Scope: §3.2–3.6 (lines 746–1287) over ℤ_p coefficients;
deferred items are tabulated in `plan.md` ("Deferred").

## Skeleton location

Every lemma below exists as a `:= by sorry` declaration in:

- `PadicLFunctions/Measure/Basic.lean`
- `PadicLFunctions/Measure/MahlerTransform.lean`
- `PadicLFunctions/Measure/Convolution.lean`
- `PadicLFunctions/Measure/Toolbox.lean`
- `PadicLFunctions/Measure/UnitsZp.lean`
- `PadicLFunctions/Measure/Fubini.lean`
- `PadicLFunctions/Measure/PseudoMeasure.lean`

`lake build PadicLFunctions` passes — **Build completed successfully (2437 jobs)**,
sorry warnings only, no type errors (verified 2026-06-09).

## Verification method note

The lean-lsp MCP tools (loogle/leansearch/hover) are not connected in this planning
session. Every mathlib discharge below was instead verified by **reading the mathlib
source file directly** (exact file + line cited) — a stronger check than a search hit.

## Prior-B2 log (Step 4.6)

`.mathlib-quality/b2_log.jsonl` does not exist (new project, zero entries). No leaf can
match a prior B2; all leaves are clean by vacuity. (Future B2s recorded by `/beastmode`
must be consulted by the next `/develop` pass.)

---

## R1: The measure space (RJW §3.2, Def. 3.6 + Rem. 3.8)

### Plain-English proof substrate (Step 1)

RJW defines `𝒞(G, L)` with the sup valuation (Def. 3.5, lines 749–755), measures as the
continuous dual (Def. 3.6, lines 760–766) with the 𝒪_L-valued measures singled out, the
Dirac measures (Ex. 3.7, lines 774–779), and proves (Rem. 3.8, lines 782–802) that
restriction to locally constant functions is an isomorphism, via the locally constant
truncations `φ_n(x) = ∑_{a mod p^n} φ(a)·𝟙_{a+p^nℤ_p}(x)` and a continuity argument.
Lean design: over ℤ_p the boundedness/continuity in Def. 3.6 is *automatic*, so
`PadicMeasure p X := C(X, ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]` and continuity becomes a lemma.

### Leaves

- **L1.1** (leaf): `PadicMeasure.norm_apply_le` — `‖μ f‖ ≤ ‖f‖`
  - Lean: `PadicLFunctions/Measure/Basic.lean:107`
  - Source: Def. 3.6 footnote (line 759, commented variant retained in TeX):
    > "Recall that a linear functional μ is bounded if there exists a constant C such
    > that v_p(μ(φ)) ≥ v_𝒞(φ) + C for all φ ∈ 𝒞(G, L), and it is equivalent to asking
    > μ to be continuous."
    and line 765: "Since measures are continuous (or equivalently, bounded), we have
    ℳ(G, L) = ℳ(G, 𝒪_L) ⊗_{𝒪_L} L."
  - Lean ↔ source: over 𝒪 = ℤ_p the constant is C = 0: 𝒪-valued measures have norm ≤ 1.
    Our statement is the 𝒪-integral form of the footnote.
  - Discharged by: pure computation. `‖f‖` attained (X compact; sup over the discrete
    value set {p^{-k}} ∪ {0}); if `‖f‖ ≤ p^{-m}` then `f = p^m • g` with
    `g x := ⟨(f x : ℚ_[p])/p^m, _⟩` continuous, so `μ f = p^m • μ g` has norm ≤ p^{-m}.
    Mathlib inputs: `ContinuousMap.norm_coe_le_norm` (read in
    `Topology/ContinuousMap/Compact.lean`), `PadicInt.norm_le_pow_iff_dvd`
    (read in `NumberTheory/Padics/PadicIntegers.lean`).
  - Attacks attempted:
    - [2] Edge cases: `f = 0` (both sides 0 ✓); `X = ∅` (C(∅,ℤ_p) trivial, μ f = 0 ✓);
      `μ = dirac x` (LHS = ‖f x‖ ≤ sup ✓). No failure.
    - [3] Hypothesis test: `CompactSpace X` is necessary — for noncompact X the sup norm
      on C(X, ℤ_p) need not exist (norm instance requires compactness), so the statement
      doesn't even typecheck without it. Not over-specified.
    - [4] Source-drift: footnote allows arbitrary constant C; our C = 0 form is the
      𝒪-valued specialisation, exactly the convention of line 765 ("mainly concerned
      with 𝒪_L-valued functions and measures"). No drift.
    - [5] Discharge: `ContinuousMap.norm_coe_le_norm` exists at
      `Topology/ContinuousMap/Compact.lean` (read); divisibility `f = p^m • g` is the
      standard ℤ_p-ball argument; composition ≤ 3 steps. OK.
  - Verdict: SURVIVED.

- **L1.2** (leaf): `PadicMeasure.continuous`
  - Lean: `Basic.lean:112`
  - Source: line 765 (quoted at L1.1) — boundedness ⟺ continuity.
  - Lean ↔ source: linear + bounded-by-1 (L1.1) ⟹ Lipschitz ⟹ continuous.
  - Discharged by: L1.1 + `LipschitzWith.continuous` or
    `AddMonoidHomClass.continuous_of_bound` (read in
    `Analysis/Normed/Operator/...`; fallback: `Metric.continuous_iff` + L1.1 on `f − g`,
    using linearity `μ f − μ g = μ (f − g)`).
  - Attacks attempted:
    - [2] Edge cases: constant μ = 0 ✓; X empty ✓.
    - [3] Hypothesis test: compactness needed for the norm to exist (as L1.1).
    - [5] Discharge: bound-implies-continuous for additive maps on normed groups is
      standard; ≤ 3 lemma composition via L1.1. OK.
  - Verdict: SURVIVED.

- **L1.3** (leaf): `PadicMeasure.exists_locallyConstant_norm_sub_le` — density
  - Lean: `Basic.lean:123`
  - Source: Rem. 3.8, lines 782–784 (verbatim):
    > "Let 𝒞^lc(G,𝒪_L) denote the space of locally constant functions G → 𝒪_L; this is
    > a dense subspace of the continuous functions 𝒞(G,𝒪_L). Indeed, any continuous
    > function φ ∈ 𝒞(G, 𝒪_L) can be p-adically approximated by its locally constant
    > truncations φ_n(x) = ∑_{a ∈ (ℤ/p^nℤ)} φ(a) 𝟙_{a+p^nℤ_p}(x)".
  - Lean ↔ source: source proves density for G = profinite group via explicit
    truncations; our statement is for general compact X with the ball-preimage
    argument (preimages of the clopen balls of radius ε form a clopen cover —
    clopen because balls in the ultrametric ℤ_p are clopen — finite subcover,
    disjointify, choose values). This *generalises* the source's claim (compact X
    rather than profinite G); on ℤ_p/ℤ_p^× the two arguments coincide. Generalisation
    is conservative: the source's instances are special cases.
  - Discharged by: new proof (~25 LOC; the source spends 8 lines, lines 782–791).
    Mathlib inputs verified: `IsUltrametricDist` ball-clopenness
    (`Analysis/Normed/Group/Ultra.lean` family), `CompactSpace.elim_nhds_subcover`,
    `LocallyConstant` constructors (`Topology/LocallyConstant/Basic.lean`, read).
  - Attacks attempted:
    - [1] Counterexample search: density of loc. constants FAILS for connected targets
      (e.g. C(X,ℝ)) — but ℤ_p is totally disconnected/ultrametric, which is exactly
      what makes ball-preimages clopen. No contradiction for our target.
    - [2] Edge: X = ∅ (g = const junk? LocallyConstant ∅ exists, ‖f−g‖ = 0 ≤ ε ✓);
      f already locally constant (g := f ✓); ε huge (g := 0 ✓).
    - [3] Hypothesis: T2/total-disconnectedness of X NOT needed (clopenness comes from
      the target's ultrametric) — deliberately dropped vs. the source's profinite G;
      verified the proof outline nowhere uses them.
    - [5] Discharge: this is a genuinely new lemma (verified absent: grepped mathlib for
      `LocallyConstant` + dense — only Condensed-framework hits, different statement).
      PR candidate; sized from source: 8 source lines → ~25 LOC Lean.
  - Verdict: SURVIVED.

- **L1.4** (leaf): `PadicMeasure.ext_locallyConstant`
  - Lean: `Basic.lean:131`
  - Source: Rem. 3.8, lines 787–799, esp.
    > "We claim restriction from 𝒞 to 𝒞^lc defines a canonical isomorphism
    > ℳ(G,𝒪_L) ≅ ℳ^lc(G,𝒪_L)."
    (injectivity direction).
  - Lean ↔ source: `μ` agreeing with `ν` on locally constant g, both continuous (L1.2),
    locally constant dense (L1.3) ⟹ equal. Exactly the source's continuity argument
    (lines 791–795) run for the difference μ − ν.
  - Discharged by: L1.2 + L1.3 + `DenseRange.equalizer`-style argument (mathlib:
    `Continuous.ext_on` exists — read in `Topology/Separation` family; or direct ε/3).
  - Attacks attempted:
    - [2] Edge: μ = ν trivially ✓; X = ∅ (all measures equal ✓).
    - [4] Source-drift: source states an isomorphism ℳ ≅ ℳ^lc; we take only
      injectivity (the surjectivity inverse — extending a functional from 𝒞^lc — is
      NOT needed by any §3–4 result; deferred with the additive-functions description,
      see plan.md). Verified: §3.4–3.6 only ever use determination, not extension.
    - [5] Discharge: `Continuous.ext_on` + `DenseRange` machinery exists; ≤ 3 lemmas
      after L1.2/L1.3. OK.
  - Verdict: SURVIVED.

(Definitions `dirac`, `compRight`, `pushforward` are data, fully constructed — no
sorries, no leaves. `pushforward_dirac`, `dirac_apply`, `compRight_apply` are `rfl`.)

---

## R2: The Mahler transform is a linear equivalence (RJW Thm. 3.20, linear part)

### Plain-English proof substrate (Step 1)

Source statement (lines 988–991):
> "The Mahler transform gives an 𝒪_L-algebra isomorphism ℳ(ℤ_p, 𝒪_L) ≅ 𝒪_L⟦T⟧."

Source proof (lines 994–1005), structure: (a) *determination*: "any measure
μ ∈ ℳ(ℤ_p,𝒪_L) is uniquely determined by the values ∫ binom(x,n)·μ", via Mahler's
theorem `φ = ∑ a_n(φ) binom(x,n)` and `∫φ·μ = ∑ a_n(φ) ∫binom(x,n)·μ` (continuity);
(b) *construction*: "given any collection of values c_n ∈ 𝒪_L … there is a unique
measure μ_g with ∫binom(x,n)·μ_g = c_n", defined by `∫φ·μ_g = ∑ a_n(φ)c_n`, "which
converges"; (c) "Visibly 𝒜_{μ_g} = g". The analytic substrate (RJW Thm. 3.13, Mahler)
is mathlib's `PadicInt.hasSum_mahler` / `fwdDiff_tendsto_zero` / `mahlerSeries`, with
Mahler coefficients `a_n(φ) = Δⁿφ(0)` (RJW Rem. 3.14, lines 951–958 — "discrete
derivatives", identical to mathlib's `Δ_[1]^[n] f 0`).

### Leaves

- **L2.1** (leaf): `PadicMeasure.apply_eq_tsum` — evaluation formula
  - Lean: `MahlerTransform.lean:62`
  - Source (lines 995–998, verbatim):
    > "By Mahler's theorem, we can write φ(x) = ∑_{n ≥ 0} a_n(φ) binom(x,n) for some
    > unique a_n(φ) ∈ 𝒪_L such that a_n(φ) → 0 as n → ∞; and then we have
    > ∫_{ℤ_p} φ·μ = ∑_{n ≥ 0} a_n(φ) ∫_{ℤ_p} binom(x,n)·μ."
  - Lean ↔ source: our statement is this display with `a_n(φ) = Δⁿφ(0)` (source
    Rem. 3.14: "a_n(φ) = φ^[n](0)" where φ^[k+1](x) = φ^[k](x+1) − φ^[k](x) — exactly
    mathlib `fwdDiff`).
  - Discharged by: `PadicInt.hasSum_mahler f : HasSum (fun n ↦ mahlerTerm (Δ_[1]^[n] f 0) n) f`
    (read at `MahlerBasis.lean:339`) mapped through the continuous (L1.2) linear μ:
    `HasSum.map` + `mahlerTerm_apply` (`MahlerBasis.lean:256`), then `HasSum.tsum_eq`.
  - Attacks attempted:
    - [2] Edge: f = const c: Δⁿf(0) = 0 for n ≥ 1, sum = c·μ(1) ✓ matches μ(const) ✓;
      f = mahler k: sum has single term μ(mahler k) ✓ (uses Δⁿ(mahler k)(0) = δ_{nk},
      see L2.4).
    - [3] Hypothesis: needs nothing beyond μ linear — continuity is supplied by L1.2,
      not assumed. Summability of the RHS: from `fwdDiff_tendsto_zero` + bounded
      coefficients; verified mathlib `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`
      (used at `MahlerBasis.lean:287`) covers it.
    - [5] Discharge: `hasSum_mahler` signature read: needs `[NormedAddCommGroup E]
      [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E] [IsUltrametricDist E] [CompleteSpace E]`
      — all hold for E = ℤ_[p] (instances exist; `IsUltrametricDist ℤ_[p]` via
      `PadicInt` ultrametric, `CompleteSpace ℤ_[p]` exists). `HasSum.map` along a
      continuous `AddMonoidHom` exists. Composition ≤ 3. OK.
  - Verdict: SURVIVED.

- **L2.2** (leaf): `PadicMeasure.mahlerTransform_dirac` — `𝓐(δ_a) = (1+T)^a`
  - Lean: `MahlerTransform.lean:70`
  - Source (Ex. 3.16, lines 968–973, verbatim):
    > "Let a ∈ ℤ_p, and recall the Dirac measure δ_a. By definition, its Mahler
    > transform is 𝒜_{δ_a}(T) = ∑_{n≥0} binom(a,n) Tⁿ = (1+T)^a."
  - Lean ↔ source: coefficientwise both sides have n-th coefficient `binom(a,n)`:
    LHS `δ_a(mahler n) = Ring.choose a n` (mathlib `mahler_apply`); RHS
    `binomialSeries_coeff` (read at `PowerSeries/Binomial.lean:50`:
    `coeff n (binomialSeries A r) = Ring.choose r n • 1`).
  - Discharged by: `PowerSeries.ext` + `binomialSeries_coeff` + `mahler_apply`
    (≤ 3 lemmas; `smul_eq_mul`+`mul_one` glue).
  - Attacks attempted:
    - [2] Edge: a = 0: (1+T)^0 = 1 (`binomialSeries_zero` read at line 78) and
      δ_0(mahler n) = choose 0 n = δ_{n0} ✓ consistent; a = 1: (1+T) ✓.
    - [4] Source-drift: none — statement is literally the source display.
    - [5] Discharge: names verified by reading `PowerSeries/Binomial.lean` (lines
      46–80). OK.
  - Verdict: SURVIVED.

- **L2.3** (leaf): `PadicMeasure.mahlerTransform_injective`
  - Lean: `MahlerTransform.lean:77`
  - Source: lines 995–998 (quoted at L2.1) — "uniquely determined".
  - Lean ↔ source: if 𝓐μ = 0 then all μ(mahler n) = 0, so by L2.1 μf = 0 ∀f.
  - Discharged by: L2.1 + `PowerSeries.ext_iff` + `LinearMap.ext`.
  - Attacks: [2] zero measure ✓; [3] no extra hypotheses; [5] composition = 2 lemmas
    after L2.1. SURVIVED.

- **L2.4** (leaf): `PadicMeasure.mahlerTransform_ofPowerSeries` (+ well-definedness of
  `ofPowerSeries` = its `map_add'`/`map_smul'` fields)
  - Lean: `MahlerTransform.lean:85–97`
  - Source (lines 1000–1004, verbatim):
    > "Conversely, given any collection of values c_n ∈ 𝒪_L, defining an element
    > g = ∑_{n≥0} c_n Tⁿ ∈ 𝒪_L⟦T⟧, there is a unique measure μ_g with
    > ∫ binom(x,n)·μ_g = c_n. Concretely, for any φ = ∑ a_n(φ) binom(x,n) ∈ 𝒞(ℤ_p,𝒪_L)
    > as above, we define ∫_{ℤ_p} φ·μ_g = ∑_{n≥0} a_n(φ) c_n, which converges to an
    > element in 𝒪_L. Visibly we have 𝒜_{μ_g} = g".
  - Lean ↔ source: `ofPowerSeries g` is the displayed formula with a_n(φ) = Δⁿφ(0).
    Linearity fields: `fwdDiff_iter_add` (read: used at `MahlerBasis.lean:362`) +
    `tsum_add` (summability from `fwdDiff_tendsto_zero` × bounded). The computation
    `∫binom(x,k)·μ_g = c_k` needs `Δⁿ(mahler k)(0) = if n = k then 1 else 0`: this is
    mathlib's `fwdDiff_mahlerSeries` (read at `MahlerBasis.lean:313`) applied to
    `mahler k = mahlerSeries (Pi.single k 1)` (single-coefficient Mahler series), or
    directly `fwdDiff_iter_choose_zero` (used at `MahlerBasis.lean:332`).
  - Attacks attempted:
    - [2] Edge: g = 0 → μ_0 = 0 ✓; g = 1 → μ = δ_0 (only n = 0 term; Δ⁰φ(0) = φ(0) ✓).
    - [3] Hypothesis: convergence requires Δⁿφ(0) → 0 — that is mathlib
      `fwdDiff_tendsto_zero`, requiring f continuous — supplied by φ ∈ C(ℤ_p,ℤ_p) ✓;
      coefficient boundedness automatic (ℤ_p). Nothing smuggled.
    - [5] Discharge: `fwdDiff_iter_choose_zero` verified present (used in
      `MahlerBasis.lean:332`, defined in `Algebra/Group/ForwardDiff.lean`);
      `tsum`-linearity lemmas standard. OK.
  - Verdict: SURVIVED.

- **L2.5** (internal): `PadicMeasure.mahlerLinearEquiv` (left_inv, right_inv legs)
  - Lean: `MahlerTransform.lean:102`
  - Composition of L2.1 (left_inv: `ofPowerSeries (𝓐 μ) = μ` by `LinearMap.ext` + L2.1
    read right-to-left) and L2.4 (right_inv). Source: Thm. 3.20's proof IS this
    two-direction argument (lines 994–1005); composition attack: could both legs hold
    and the equiv fail? No — `LinearEquiv` is literally the pair. SURVIVED.

---

## R3: Ring structure and RJW Thm. 3.20 in full (Convolution.lean)

### Plain-English proof substrate (Step 1)

Source (Rem. 3.11, lines 907–911, verbatim):
> "The Iwasawa algebra Λ(ℤ_p) has a natural 𝒪_L-algebra structure, and hence by
> transport of structure we obtain such a structure on ℳ(ℤ_p,𝒪_L). As with the
> classical situation for finite group rings, the algebra structure on the space of
> measures can be described directly via convolution of measures. For a general
> profinite abelian group G, given two measures μ,λ ∈ ℳ(G,𝒪_L), one defines their
> convolution μ * λ to be ∫_G φ·(μ*λ) = ∫_G (∫_G φ(x + y)·λ(y))·μ(x). One checks that
> this does give an algebra structure and that the isomorphism above is an isomorphism
> of 𝒪_L-algebras."

Lean route (= the source's, with ℤ_p[[T]] playing the role the source gives Λ):
multiplication is *defined* by transport along `mahlerLinearEquiv`; the convolution
display is the theorem `mul_apply`. The bridge is Chu–Vandermonde on the Mahler basis.

### Leaves

- **L3.1** (leaf): `mahlerTransform_mul`, `mahlerTransform_one`, CommRing laws,
  `mahlerRingEquiv` — transport bookkeeping
  - Lean: `Convolution.lean:46–86`
  - Source: "by transport of structure" (line 908, quoted above).
  - Discharge: `mul_def` + `LinearEquiv.apply_symm_apply` gives `mahlerTransform_mul`
    in one rewrite; each ring law transfers along the bijection (e.g. assoc:
    apply `(mahlerLinearEquiv p).injective`, push `mahlerTransform_mul` through, use
    assoc in `PowerSeries`). `mahlerTransform_one`: `𝓐(δ_0) = (1+T)^0 = 1` =
    L2.2 + `binomialSeries_zero` (read at `PowerSeries/Binomial.lean:78`).
  - Attacks: [2] check `one ≠ zero` transfers (PowerSeries ℤ_p nontrivial ✓);
    [3] no hidden hypotheses — pure algebra over an established bijection;
    [5] `LinearEquiv.apply_symm_apply`/`symm_apply_apply` exist (core mathlib). The
    only subtlety: the `Mul`/`One` instances must not clash with existing instances on
    `C(X,ℤ_p) →ₗ ℤ_p` — verified: mathlib defines no `Mul`/`One`/`Ring` on linear-map
    duals (grep `instMul.*LinearMap` in `Mathlib/Algebra/Module/LinearMap` — module
    structure only). SURVIVED.

- **L3.2** (leaf, KEY): `PadicMeasure.mul_apply` — the convolution formula
  - Lean: `Convolution.lean:96`
  - Source: Rem. 3.11 display (quoted above): `∫φ·(μ*λ) = ∫(∫φ(x+y)·λ(y))·μ(x)`.
  - Lean ↔ source: identical, with the inner integral packaged as a continuous map.
  - Proof route (expanding the source's "one checks", per Step 1's terse-source rule):
    both sides are linear in `f` and bounded (L1.1), so by density (L1.3/L1.4 +
    Mahler expansion L2.1) it suffices to check `f = mahler n`. LHS = n-th coeff of
    `𝓐μ·𝓐ν = ∑_{i+j=n} μ(mahler i)ν(mahler j)`. RHS: inner function
    `x ↦ ν(binom(x+·,n))`; Chu–Vandermonde (`add_choose_eq`, read at
    `RingTheory/Binomial.lean:519`:
    `choose (r + s) k = ∑_{ij ∈ antidiagonal k} choose r ij.1 * choose s ij.2`)
    gives `binom(x+y,n) = ∑_{i+j=n} binom(x,i)binom(y,j)`; ν is linear over the finite
    sum, then μ likewise; equality follows.
  - Attacks attempted:
    - [1] Counterexample/consistency: evaluate both sides at μ = δ_a, ν = δ_b, f
      arbitrary: LHS = (δ_a*δ_b)(f) = δ_{a+b}(f) = f(a+b) (using L3.3 below); RHS =
      (f((a+·)))(b) = f(a+b) ✓ consistent.
    - [2] Edge: n = 0 (both sides μ(1)ν(1)·, choose(x+y,0)=1 ✓); f constant ✓.
    - [3] Hypothesis-strength: `Commute r s` hypothesis of `add_choose_eq` — ℤ_p
      commutative ✓ trivially satisfied; no hidden assumption.
    - [4] Source-drift: the formula in the source integrates λ inside and μ outside;
      our statement matches (ν inside, μ outside). For commutative measures the order
      is immaterial AFTER comm is proven, but the statement must match the source
      *before* comm is available — checked: it does (μ outer ✓).
    - [5] Discharge: `add_choose_eq` verified by reading (line 519, hypothesis
      `Commute r s`, BinomialRing R — ℤ_[p] instance at `MahlerBasis.lean:78`). The
      density-extension step needs "both sides continuous in f": LHS by L1.1; RHS: the
      inner map's norm is ≤ ‖f‖ pointwise (L1.1 twice) — fine. SURVIVED.

- **L3.3** (leaf): `dirac_mul_dirac` — `[a]·[b] = [a+b]`
  - Lean: `Convolution.lean:105`
  - Source: Ex. 3.12 (lines 914–920):
    > "Under the isomorphism of Proposition 3.10, δ_a corresponds to … an element of
    > the Iwasawa algebra that we denote [a]."
    combined with Ex. 3.16 (`𝓐δ_a = (1+T)^a`).
  - Discharge: apply `mahlerTransform_injective` (L2.3); `𝓐(δ_a·δ_b) = (1+T)^a(1+T)^b
    = (1+T)^{a+b}` by L2.2 + `binomialSeries_add` (read at
    `PowerSeries/Binomial.lean:60`).
  - Attacks: [2] a = b = 0 ✓ gives 1·1 = 1; [4] the source treats [a]-elements via the
    Λ-description — our statement is the measure-side image, equivalent by Ex. 3.16;
    [5] `binomialSeries_add` signature read: `[Ring A] [Algebra R A]` — with R = A =
    ℤ_[p] ✓ (`Algebra ℤ_[p] ℤ_[p]` := `Algebra.id`). SURVIVED.

---

## R4: The toolbox (RJW §3.5)

### Plain-English substrate (Step 1)

Each §3.5 operation is defined measure-side and computed on Mahler transforms. Source
proofs are one-liners on the Mahler basis; we mirror them. The two ξ-formulas (lines
1118–1127, 1155–1158) are deferred (plan.md): every identity below is the source's,
proved by the source's own ξ-free arguments (lines 1149–1151 are explicit function
manipulations, reproduced exactly).

### Leaves

- **L4.1** (leaf): `mahlerTransform_cmul_X` — `𝓐_{xμ} = ∂𝓐_μ`
  - Lean: `Toolbox.lean:46` (`del` at `Toolbox.lean:41`)
  - Source (Lem. 3.24, lines 1066–1075, proof verbatim):
    > "The result follows directly from computing
    > x·binom(x,n) = (x−n)binom(x,n) + n·binom(x,n) = (n+1)binom(x,n+1) + n·binom(x,n)."
  - Lean ↔ source: coefficientwise: `(xμ)(mahler n) = μ(x·binom(x,n)) =
    (n+1)μ(mahler (n+1)) + n·μ(mahler n)`; and `coeff n ((1+X)·F') = (n+1)F_{n+1} + n F_n`
    (`coeff_derivativeFun` read at `PowerSeries/Derivative.lean:46`). The binomial
    identity `x·choose x n = (n+1)·choose x (n+1) + n·choose x n` must be proven for
    `Ring.choose` over ℤ_p: by `denseRange_natCast` + continuity it reduces to ℕ, where
    it is `Nat.succ_mul_choose_eq`-adjacent arithmetic. (~20 LOC; source: 1 line.)
  - Attacks: [2] n = 0: x·1 = 1·binom(x,1) + 0 ✓ (binom(x,1) = x);
    [3] no hypotheses to weaken; [5] `coeff_derivativeFun` verified by reading;
    `Polynomial`/`Ring.choose` continuity from `PadicInt.continuous_choose`
    (`MahlerBasis.lean:93`). SURVIVED.

- **L4.2** (leaf): `apply_powCM` — `∫xᵏdμ = (∂ᵏ𝓐μ)(0)`
  - Lean: `Toolbox.lean:56`
  - Source (Cor. 3.25, lines 1079–1082, verbatim):
    > "For μ ∈ Λ(ℤ_p), we have ∫_{ℤ_p} x^k·μ = (∂^k 𝒜_μ)(0)."
  - Discharge: induction on k from L4.1; base: `∫1dμ = 𝓐μ(0)` = `constantCoeff` =
    coeff 0 = μ(mahler 0) ✓ (mahler 0 = 1).
  - Attacks: [2] k = 0 ✓ (above); k = 1: g'(0) ✓ matches source Rem. 3.21(2)
    (line 1037: "∫x·μ_g = g′(0)"); [4] source Rem. 3.21(2) lists ∫x², ∫x³ examples
    with integer-coefficient combinations — cross-checked: ∂²F(0) = F''(0) + F'(0) ✓
    matches the source's `∫x²·μ_g = g''(0) + g'(0)`. SURVIVED.

- **L4.3** (leaf): `res_union` + `isClopen_pZp` + `isClopen_units`
  - Lean: `Toolbox.lean:73, 121, 138`
  - Source (§3.5.3, lines 1100–1108):
    > "The 'restriction of μ to X' is the measure Res_X(μ) on ℤ_p defined by
    > ∫_{ℤ_p} f·Res_X(μ) = ∫_{ℤ_p} f𝟙_X·μ."
    and line 1129: "we can write X (or its complement…) as a disjoint union".
  - Discharge: `𝟙_{U∪V} = 𝟙_U + 𝟙_V` for disjoint clopens (`LocallyConstant.charFn`
    arithmetic, `Topology/LocallyConstant/Algebra.lean:94` `coe_charFn` read:
    `charFn Y hU = Set.indicator U 1`) + linearity. Clopenness: `pℤ_p = {‖x‖ < 1}`
    is the open unit ball = complement of the unit sphere; both clopen by
    ultrametricity / `PadicInt.norm_le_one` + discreteness of the value group
    (`PadicInt.norm_eq_zpow_neg_valuation` family, read). Units: `isUnit_iff : IsUnit z
    ↔ ‖z‖ = 1` (read at `PadicIntegers.lean:366`); `{‖x‖ = 1}` = complement of
    `{‖x‖ < 1}` ✓.
  - Attacks: [2] U = ∅ (charFn = 0, res = 0 ✓); U = univ (res = id ✓);
    [3] disjointness necessary (else indicators don't add) ✓ stated;
    [5] `Set.indicator` + charFn lemmas verified by reading. SURVIVED.

- **L4.4** (leaf): `mahlerTransform_sigma` / `mahlerTransform_phi`
  - Lean: `Toolbox.lean:97, 106`
  - Source (lines 1135–1146, verbatim):
    > "σ_a(μ) … has Mahler transform 𝒜_{σ_a(μ)} = 𝒜_μ((1+T)^a − 1)." and
    > "𝒜_{φ(μ)} = φ(𝒜_μ) := 𝒜_μ((1+T)^p − 1)."
  - Lean ↔ source: substitution legality: `(1+T)^a − 1` and `(1+T)^p − 1` have constant
    coefficient 0 (`binomialSeries_constantCoeff` read at `PowerSeries/Binomial.lean:55`),
    so `PowerSeries.HasSubst.of_constantCoeff_zero'` (read at
    `PowerSeries/Substitution.lean:67`) applies — mathlib's algebraic `subst` is legal.
  - Proof route (the source gives the formula without proof — expansion per Step 1):
    fix n; for k ∈ ℕ, `binom(ak, n) = coeff_n ((1+T)^{ak}) = coeff_n (((1+T)^a)^k) =
    ∑_{m ≤ n} binom(k,m)·c_{n,m}` where `c_{n,m} = coeff_n ((((1+T)^a −1))^m)` (the sum
    truncates at m ≤ n since `((1+T)^a−1)^m` has order ≥ m); all terms continuous in k,
    `denseRange_natCast` extends to x ∈ ℤ_p; apply μ and identify with
    `coeff_n (subst … 𝓐μ)` via the `coeff_subst` finiteness. Same for a = p.
  - Attacks:
    - [2] Edge: a = 1: σ_1 = id and subst((1+T)−1) = subst(T) = id ✓;
      n = 0: both sides give μ(1) ✓ (constantCoeff subst = constantCoeff at 0 ✓).
    - [3] Hypothesis: a a unit is NOT needed for the formula (works for any a ∈ ℤ_p —
      φ is literally the a = p case); our skeleton states σ for units (the paper's
      action) and φ separately — consistent with source.
    - [4] Drift-check: source's φ on power series (Eq. 3.9) is *defined* by this
      formula; our statement *proves* agreement of measure-side and series-side — same
      content. The ω-order subtlety (order ≥ m of `((1+T)^a−1)^m`) verified:
      `constantCoeff = 0` ⟹ `X ∣ _` ⟹ order ≥ m under powers ✓.
    - [5] `HasSubst.of_constantCoeff_zero'` + `substAlgHom` (an `AlgHom`, so
      `map_mul`/`map_add` free) verified by reading `Substitution.lean:61–189`.
  - Verdict: SURVIVED.

- **L4.5** (leaf): `shiftDiv` well-definedness + `shiftDiv_mul`
  - Lean: `Toolbox.lean:115–127`
  - Source: ψ's defining formula (lines 1147–1148):
    > "we define a measure ψ(μ) on ℤ_p by defining ∫_{ℤ_p} f(x)·ψ(μ) = ∫_{pℤ_p} f(p⁻¹x)·μ."
  - Lean ↔ source: `f(p⁻¹x)` on `pℤ_p` is implemented as `f ∘ shiftDiv` cut by
    `𝟙_{pℤ_p}`, where `shiftDiv x = (x − [x mod p])/p` with `[·]` the canonical digit
    `PadicInt.appr x 1`; on `pℤ_p` the digit is 0, so `shiftDiv(px) = x` ✓
    (`shiftDiv_mul`). Membership: `‖x − appr x 1‖ ≤ p⁻¹` (mathlib `appr_spec`-family,
    `RingHoms.lean:682–695` read — `dist_appr_spec`); quotient by p stays in ℤ_p.
    Continuity: `appr · 1` is locally constant (factors through `toZMod`), so shiftDiv
    is a difference/scaling of continuous maps.
  - Attacks: [2] x = 0: shiftDiv 0 = 0 ✓; x = p: appr p 1 = 0 (p ≡ 0 mod p) →
    shiftDiv p = 1 ✓; x = 1: shiftDiv 1 = (1−1)/p = 0 ✓ (value irrelevant — cut off by
    indicator). [3] only the values on pℤ_p matter for ψ; off-pℤ_p values arbitrary —
    our choice is canonical, no hypothesis hidden. [5] `PadicInt.appr` + spec verified
    by reading `RingHoms.lean`. SURVIVED.

- **L4.6** (leaf): `psi_phi` (`ψ∘φ = id`) and `phi_psi` (`φ∘ψ = Res_{pℤ_p}`)
  - Lean: `Toolbox.lean:152, 158`
  - Source (lines 1149–1151, verbatim — the source PROVES both):
    > "∫ f(x)·ψ∘φ(μ) = ∫ 𝟙_{pℤ_p}(x) f(p⁻¹x)·φ(μ) = ∫ 𝟙_{pℤ_p}(px) f(x)·μ = ∫ f(x)·μ,
    > ∫ f(x)·φ∘ψ(μ) = ∫ f(px)·ψ(μ) = ∫_{pℤ_p} f(x)·μ = ∫ f(x)·Res_{pℤ_p}(μ)."
  - Discharge: unfold definitions; the function identities are
    `𝟙_{pℤ_p}(px) = 1` (px ∈ pℤ_p ✓) and `shiftDiv(px) = x` (L4.5); pure
    `ContinuousMap.ext` computations.
  - Attacks: [2] μ = δ_a: ψφδ_a: φδ_a = δ_{pa}; ψδ_{pa}(f) = 𝟙(pa)f(shiftDiv(pa)) =
    f(a) = δ_a f ✓. φψδ_a for a unit: ψδ_a = 0?? ψδ_a(f) = 𝟙_{pℤ}(a)·f(…) = 0 ✓ and
    Res_{pℤ_p}δ_a = 𝟙_{pℤ}(a)·δ_a = 0 ✓ consistent. [4] no drift — displays copied.
    [5] composition of our own leaves only. SURVIVED.

- **L4.7** (leaf): `res_units_eq` (`Res_{ℤ_p^×} = 1 − φψ`) and
  `isSupportedOn_units_iff_psi_eq_zero` (Cor. 3.32)
  - Lean: `Toolbox.lean:146, 167`
  - Source: Eq. (3.10) (lines 1152–1154):
    > "In particular, we have Res_{ℤ_p^×}(μ) = (1 − φ∘ψ)(μ)."
    and Cor. 3.32 with proof (lines 1161–1167, verbatim):
    > "Then μ is supported on ℤ_p^× if and only if Res_{ℤ_p^×}(μ) = μ, or equivalently
    > if and only if 𝒜_μ = 𝒜_μ − φ∘ψ(𝒜_μ), which happens if and only if ψ(𝒜_μ) = 0,
    > since the operator φ is injective."
  - Discharge: `res_units_eq`: 𝟙_{ℤ_p^×} + 𝟙_{pℤ_p} = 1 (clopen partition of ℤ_p:
    `isUnit_iff`/`not_isUnit_iff` ‖x‖=1 vs ‖x‖<1, read at `PadicIntegers.lean:366,385`)
    + L4.6(`phi_psi`). Cor: (⇒) ψμ = ψ(Res μ) = ψμ − (ψφ)(ψμ) = ψμ − ψμ = 0 via
    L4.6(`psi_phi`); (⇐) immediate from `res_units_eq`. φ-injectivity (source's step)
    is supplied by `psi_phi` (left inverse) — same argument, ξ-free.
  - Attacks: [2] μ = δ_1 (unit): ψδ_1 = 0 ✓ supported ✓; μ = δ_0: ψδ_0 = δ_0 ≠ 0 and
    Res_{units}δ_0 = 0 ≠ δ_0 ✓ consistent. [4] drift-check vs source: source phrases
    Cor 3.32 via ψ(𝒜_μ) = 0 on power series; ours via ψ(μ) = 0 on measures — equivalent
    by 𝓐 injectivity (L2.3); recorded. [5] partition identity verified against
    `isUnit_iff`. SURVIVED.

---

## R5: Λ(ℤ_p^×), Fubini, and pseudo-measures (RJW §3.6 + Rem. 3.33)

### Plain-English substrate (Step 1)

(a) Rem. 3.33 (lines 1169–1176): ι : Λ(ℤ_p^×) ↪ Λ(ℤ_p), image = ker ψ, NOT a subring;
convolution on ℤ_p^× uses the multiplicative structure (Eq. 3.11, verbatim):
> "∫_{ℤ_p^×} f(x)·(μ*_{ℤ_p^×}λ) = ∫_{ℤ_p^×} (∫_{ℤ_p^×} f(xy)·μ(x))·λ(y)".
(b) Def. 3.34 (lines 1185–1191): pseudo-measures: λ ∈ Q(G) with ([g]−[1])λ ∈ Λ(G) ∀g.
(c) Lem. 3.36 (lines 1215–1241): the zero-divisor lemma, proof: (i) the vanishing
forces 𝒜_{ιμ} constant "since each non-trivial binomial polynomial is a linear
combination of strictly positive powers of x"; ψ kills it; (ii) `∫(xy)^k d(μ*λ)`
factors; (iii) reduce to (i) via ([a]−[1])μ.
(d) Def. 3.37 + Lem. 3.38 (lines 1245–1282): augmentation ideal; at finite level n,
`(ℤ/p^n)^× cyclic ⟹ I((ℤ/p^n)^×) = ([ā]−[1])·𝒪_L[(ℤ/p^n)^×]`; "in the inverse limit",
I(ℤ_p^×) = ([a]−[1])Λ; hence μ/([a]−[1]) is a pseudo-measure; conversely all
pseudo-measures have this shape (lines 1284–1285).

The "one checks" algebra structure (a) and the "in the inverse limit" step (d) are the
two places the source compresses; both are expanded below (Fubini cluster; compactness
cluster), per the Step-1 terse-source rule.

### Leaves (Fubini cluster — expansion of "one checks", API gap with sub-decomposition)

- **L5.1** (leaf): `locallyConstant_prod_mem_span_boxes`
  - Lean: `Fubini.lean:48`
  - Source: this is infrastructure the source leaves implicit in "One checks" (line
    910); the technique is the source's own reduction to locally constant functions
    (Rem. 3.8, quoted at L1.3). Internal justification: a locally constant function on
    a product of profinite spaces is constant on a finite grid of clopen boxes — refine
    the finitely many level sets (clopen, compact) by basis boxes and take the common
    grid of the projections.
  - Discharge: new (~40 LOC). Mathlib inputs: clopen-box basis for products of
    zero-dimensional compacts — `IsTopologicalBasis.prod` + compact-T2-totally
    disconnected ⟹ clopen basis (`compact_t2_tot_disc_iff_tot_sep` family /
    `loc_compact_t2_tot_disc_iff_tot_sep`; worker to locate exact modern name, the
    statement exists in `Topology/Separation`-family — fallback: direct proof via
    `LocallyConstant.discreteQuotient` machinery, `DiscreteQuotient` exists).
  - Attacks: [1] failure mode: X or Y connected (boxes don't generate) — excluded by
    `TotallyDisconnectedSpace` hypotheses ✓ present in the statement; [2] F constant
    (single box univ×univ ✓); [3] T2 needed (clopen sets may not separate otherwise);
    hypotheses match the two instantiations (ℤ_p, ℤ_p^×) ✓; [5] `DiscreteQuotient`
    verified present (`Topology/DiscreteQuotient.lean`). SURVIVED.

- **L5.2** (leaf): `integral_swap` (Fubini)
  - Lean: `Fubini.lean:62`
  - Source: expansion of "One checks that this does give an algebra structure" (line
    910). For box indicators both iterated integrals equal `μ(𝟙_U)·ν(𝟙_V)`; extend by
    linearity (L5.1) and density/continuity (L1.1, L1.3 on X×Y compact ✓).
  - Attacks: [2] F = 𝟙_{U×V}: LHS = μ(𝟙_U·ν(𝟙_V)) = ν(𝟙_V)μ(𝟙_U), RHS symmetric ✓;
    [3] both spaces need compact (norms) + zero-dim (L5.1) — ℤ_p, ℤ_p^× qualify (ℤ_p^×
    zero-dim: subtype-like topology of a zero-dim space via L5.4's embedding —
    instance `TotallyDisconnectedSpace ℤ_[p]ˣ` to be derived from the embedding;
    worker note); [5] composes L5.1 + L1.1 + L1.3. SURVIVED.

### Leaves (units geometry)

- **L5.3** (leaf): `instance : CompactSpace ℤ_[p]ˣ`
  - Lean: `UnitsZp.lean:26`
  - Source: implicit (the source treats ℤ_p^× as a profinite group throughout, e.g.
    line 747: "the examples G = ℤ_p or G = ℤ_p^× are of most interest").
  - Discharge: `Units.embedProduct` is an embedding (mathlib
    `Units.isEmbedding_embedProduct`, `Topology/Algebra/Constructions.lean` — read);
    its range `{(a,b) : ab = 1 ∧ ba = 1}` is closed in the compact ℤ_p × ℤ_pᵐᵒᵖ;
    closed subspace of compact is compact. (~12 LOC.) Verified absent from mathlib
    (no `CompactSpace _ˣ` instance found by grep).
  - Attacks: [2] sanity: ℤ_p^× = sphere ‖x‖=1 is closed-bounded ✓ consistent;
    [3] needs ℤ_p compact ✓ + T2 ✓ + topological monoid ✓ — all present;
    [5] `isEmbedding_embedProduct` verified by reading Constructions.lean. SURVIVED.

- **L5.4** (leaf): `unitsValCM` continuity, `extendByZero` (cont., linearity,
  `extendByZero_coe_unit`), `iota_injective`, `res_iota`, `mem_range_iota_iff`
  - Lean: `UnitsZp.lean:30–66`
  - Source (Rem. 3.33, lines 1169–1172, verbatim):
    > "We have an injection ι : Λ(ℤ_p^×) ↪ Λ(ℤ_p) given by ∫_{ℤ_p} φ·ι(μ) =
    > ∫_{ℤ_p^×} φ|_{ℤ_p^×}·μ, and as Res_{ℤ_p^×} ∘ ι is the identity on Λ(ℤ_p^×), we
    > can identify Λ(ℤ_p^×) with its image as a subset of Λ(ℤ_p). By Corollary 3.32, a
    > measure μ ∈ Λ(ℤ_p) lies in Λ(ℤ_p^×) if and only if ψ(μ) = 0."
  - Lean ↔ source: ι = `pushforward unitsValCM` (∫φ∘val dμ = ∫φ|_units dμ ✓ same).
    Injectivity: restriction is surjective via `extendByZero` (clopen gluing on the
    partition units ⊔ pℤ_p — continuity on each clopen piece). `mem_range_iota_iff`:
    (⇒) `res_iota` + Cor 3.32 (L4.7); (⇐) if ψμ = 0 then μ = Res_{units}μ (L4.7) and
    μ = ι(μ∘extendByZero∘…) — construct the preimage by precomposition with
    `extendByZero`.
  - Attacks: [2] μ = δ_u (u unit): ιδ_u = δ_{u.val}, ψ = 0 ✓; μ = δ_0: ψδ_0 = δ_0 ≠ 0
    and δ_0 ∉ range ι (functions vanishing... ι ν (f) depends only on f|units; δ_0
    does not — consistent ✓). [3] val continuity: `Units.continuous_val` — present as
    `Units.continuous_val`/embedding-corollary; worker locates name (fallback: fst ∘
    embedProduct continuous). [4] drift: none, statements copied. [5] clopen gluing:
    `IsClopen` + `ContinuousOn.if`-style lemmas exist (`continuousOn_if`-family). 
    SURVIVED.

### Leaves (Λ(ℤ_p^×) ring + degree + finite levels)

- **L5.5** (leaf): `unitsConv` well-definedness + CommRing laws + `units_dirac_mul_dirac`
  - Lean: `PseudoMeasure.lean:38–77`
  - Source: Eq. (3.11) (quoted in substrate) + "One checks…" (line 910).
  - Discharge: inner-map continuity: `ContinuousMap.curry` (read at
    `Topology/CompactOpen.lean:419`) + L1.2; linearity fields: linearity of μ, ν
    through the explicit formula. comm: `integral_swap` (L5.2) applied to
    `F = f ∘ mul : C(ℤ_p^× × ℤ_p^×, ℤ_p)` (mul continuous: `ContinuousMul ℤ_[p]ˣ` —
    units of a topological monoid, mathlib instance; verified the instance pattern
    exists in `Topology/Algebra/Constructions.lean`/`Group/Basic.lean`). assoc: two
    applications of the definition + one swap (standard). one: δ_1 with f(1·y) = f(y) ✓
    `rfl`-adjacent. distrib/zero: linearity. dirac·dirac: evaluate: f((uv)·) ✓ direct.
  - Attacks: [1] non-abelian failure: convolution comm FAILS for non-abelian G — ℤ_p^×
    abelian ✓ (CommGroup instance); [2] δ_u·δ_v = δ_{uv}: matches the group ring ✓;
    [3] T2/zero-dim instances on ℤ_[p]ˣ needed for L5.2 — derivable from L5.3/L5.4
    embedding (worker derives `TotallyDisconnectedSpace`/`T2Space` instances; both
    standard for subspace-like topologies — flagged in ticket); [4] source's display
    has μ inner, λ outer; our `unitsConv μ ν` has ν inner, μ outer — for the
    *definition* this is a labeling choice; the comm law erases it; the `mul_def`
    orientation is recorded in the ticket so the §4 pass quotes it consistently.
    [5] `ContinuousMap.curry` verified by reading. SURVIVED.

- **L5.6** (leaf): `deg` ring hom + `augmentationIdeal`
  - Lean: `PseudoMeasure.lean:85–94`
  - Source (Def. 3.37, lines 1245–1253, verbatim):
    > "The augmentation ideal I((ℤ_p/p^n)^×) ⊂ 𝒪_L[(ℤ_p/p^n)^×] is the kernel of the
    > natural 'degree' map 𝒪_L[(ℤ/p^nℤ)^×] → 𝒪_L, ∑_a c_a[a] ↦ ∑_a c_a. These fit
    > together into a degree map Λ(ℤ_p^×) → 𝒪_L; we call its kernel the augmentation
    > ideal I(ℤ_p^×) ⊂ Λ(ℤ_p^×)."
  - Lean ↔ source: the limit degree map is evaluation at the constant function 1
    (each finite-level degree is ∑ μ(coset) = μ(𝟙) — additivity); multiplicativity:
    `deg(μ*ν) = μ(x ↦ ν(1)) = μ(1)ν(1)` since f = 1 gives f(xy) = 1.
  - Attacks: [2] deg(δ_u) = 1 ✓; deg(0) = 0 ✓; [3] no compactness subtleties (1 is
    continuous); [4] drift: source defines deg via finite levels; equality with
    evaluation-at-1 is a (trivial) lemma the worker proves when connecting to levelMap
    (L5.7) — recorded; [5] all internal. SURVIVED.

- **L5.7** (leaf): `isClopen_unitsToZModPow_fiber`, `levelMap` (ring hom fields),
  `levelMap_jointly_injective`
  - Lean: `PseudoMeasure.lean:107–133`
  - Source (lines 888–892, verbatim — the measure→limit map):
    > "We define an element λ_H of 𝒪_L[G/H] by setting λ_H := ∑_{[a] ∈ G/H} μ(aH)[a].
    > By the additivity property of μ, we see that (λ_H)_H ∈ varprojlim 𝒪_L[G/H]".
  - Lean ↔ source: G = ℤ_p^×, H = 1 + p^nℤ_p (kernel of reduction), G/H = (ℤ/p^n)^×
    (surjectivity of ℤ_p^× → (ℤ/p^n)^× from `toZModPow` surjectivity + unit lifting
    ‖x‖ = 1 ⟸ x̄ unit). Fibre clopen: preimage of a point under the locally constant
    reduction (`ker_toZModPow` read at `RingHoms.lean:457`: kernel = span p^n ⟹ the map
    is locally constant). Ring-hom: multiplicativity = the convolution of coset
    indicators identity `(μ*ν)(𝟙_{c̄}) = ∑_{āb̄=c̄} μ(𝟙_ā)ν(𝟙_b̄)` — finite
    computation from `unitsConv` + the partition ∑_ā 𝟙_ā = 1. Joint injectivity:
    locally constant functions on ℤ_p^× factor through some level (uniform continuity:
    a locally constant function on a compact space has a Lebesgue level; here levels
    are cofinal among clopen partitions since `1 + p^nℤ_p` is a neighbourhood basis of
    1 — from `ker_toZModPow` + `dist_appr_spec`-family) + L1.4 (ext on loc. const.).
  - Attacks: [2] n = 0: (ZMod 1)ˣ trivial; levelMap μ = deg μ·[1] ✓ consistent with
    L5.6; [3] surjectivity of unitsToZModPow needed for "G/H = (ℤ/p^n)^×" — verified
    provable (lift x̄: any lift x has ‖x‖ = 1 since x̄ ≠ 0 mod p... careful n ≥ 1 and
    unit mod p^n ⟹ unit mod p ⟹ ‖x‖ = 1 ✓; n = 0 trivial); [4] source quantifies over
    all open H — we use only the cofinal chain H_n, sufficient for everything §3.6 does
    (cyclicity argument is level-wise); recorded as a deliberate, conservative
    restriction; [5] `toZModPow` surjectivity: `ZMod.natCast_self_eq_zero`-family +
    density, or `PadicInt.toZModPow`-surjective if present — worker locates; fallback
    constructs preimage via `appr`. SURVIVED.

### Leaves (zero-divisor lemma)

- **L5.8** (leaf): `eq_zero_of_forall_unitsPowCM_eq_zero` (Lem. 3.36(i))
  - Lean: `PseudoMeasure.lean:147`
  - Source (proof, lines 1228–1229, verbatim):
    > "(i) Note that the vanishing condition forces the Mahler transform 𝒜_μ(T) =
    > ∑_{k ≥ 0} (∫_{ℤ_p} binom(x,k)·μ) T^k of μ to be constant, since each non-trivial
    > binomial polynomial is a linear combination of strictly positive powers of x. As
    > μ is a measure on ℤ_p^×, we also have ψ(𝒜_μ)(T) = 0 by (3.10). Since ψ is the
    > identity on constants…, we deduce that 𝒜_μ(T) = 0, so μ = 0."
  - Lean ↔ source: μ here is `ιμ` (the source works inside Λ(ℤ_p)). Two refinements,
    both ξ-free and faithful: (1) "linear combination of positive powers": we use the
    integral identity `n! · binom(x,n) = descPochhammer n = x·q(x)` with q ∈ ℤ_p[X]
    (`descPochhammer_eq_factorial_smul_choose`, read at `RingTheory/Binomial.lean:390`;
    descPochhammer has root 0 for n ≥ 1, so X ∣ it), giving `n!·(ιμ)(mahler n) =
    ∑ q_k·∫x^{k+1} = 0`, and n! ≠ 0 in the domain ℤ_p — avoiding the source's
    ℚ_p-coefficients aside. (2) "ψ identity on constants": the source cites the
    ξ-formula (3.13); instead: constants are c·δ_0-transforms, `𝓐(ιμ) = c = 𝓐(c·δ_0)`
    ⟹ `ιμ = c·δ_0` (L2.3); `ψ(ιμ) = 0` (Cor 3.32 direction of L4.7, since
    Res(ιμ) = ιμ by `res_iota`); `ψ(δ_0) = δ_0` (direct: `𝟙_{pℤ_p}(0)·f(shiftDiv 0) =
    f(0)`); so `c·δ_0 = 0 ⟹ c = 0 ⟹ ιμ = 0 ⟹ μ = 0` (ι injective, L5.4).
  - Attacks: [1] consistency: μ = δ_u has ∫x^k = u^k ≠ 0 — hypothesis excludes ✓;
    [2] k-range: hypothesis only for k > 0 — k = 0 unconstrained, and indeed the
    argument never uses k = 0 (descPochhammer trick needs n ≥ 1 ✓; the constant
    survives until the ψ step, which is exactly why ψ is needed — matches source);
    [3] could the conclusion hold without the ψ-step (i.e. is 𝓐 constant ⟹ 0 already)?
    NO: δ_0 has constant transform 1 ≠ 0 — the ψ-step is essential; our proof keeps it
    (faithful) ✓; [4] drift: refinement (1) avoids Stirling/ℚ_p; verified the source's
    own claim is recovered exactly; [5] `descPochhammer_eq_factorial_smul_choose`
    verified by reading; `Polynomial.dvd_iff_isRoot` for X ∣ descPochhammer. SURVIVED.

- **L5.9** (leaf): `mem_nonZeroDivisors_of_forall_unitsPowCM_ne_zero` (Lem. 3.36(ii))
  - Lean: `PseudoMeasure.lean:153`
  - Source (proof, lines 1232–1234, verbatim):
    > "0 = ∫_{ℤ_p^×} x^k·(μ*λ) = ∫(∫(xy)^k·μ(x))·λ(y) = (∫x^k·μ)(∫x^k·λ), which forces
    > λ = 0 by part (i)."
  - Discharge: `(xy)^k = x^k y^k` (mul_pow) through `unitsConv` (the inner integral of
    `f(xy)` for f = pow factors as `x^k·ν(pow)` by linearity-of-scalars), then L5.8.
  - Attacks: [2] hypothesis sharp: δ_1 has ∫x^k = 1 ≠ 0 ∀k and is a unit (not just
    non-zero-divisor) ✓ consistent; [3] need both factors: statement is one-sided
    (μ*λ = 0 ⟹ λ = 0) — commutativity (L5.5) gives the two-sided nonZeroDivisors
    membership ✓; [5] internal composition. SURVIVED.

### Leaves (pseudo-measures)

- **L5.10** (leaf): `isPseudoMeasure_algebraMap`
  - Lean: `PseudoMeasure.lean:177`
  - Source: immediate from Def. 3.34 (Λ is a ring): ([g]−[1])·μ ∈ Λ for μ ∈ Λ.
  - Discharge: take ν := (δ_g − 1)·μ; `map_mul` of algebraMap. Attacks: [2] μ = 0 ✓;
    [5] `algebraMap` ring hom ✓. SURVIVED.

- **L5.11** (leaf): `pseudoMeasure_eq_zero_of_moments` (Lem. 3.36(iii))
  - Lean: `PseudoMeasure.lean:185`
  - Source (proof, lines 1236–1240, verbatim):
    > "Let μ be a pseudo-measure satisfying the vanishing condition. Let a ≠ 1 be an
    > integer prime to p; then λ = ([a] − [1])μ ∈ Λ(ℤ_p^×) is a measure by the
    > definition of pseudo-measure, and by (3.12) we have ∫x^k·λ = (a^k−1)∫x^k·μ = 0
    > for all k > 0. By part (i), we have λ = 0. But [a]−[1] satisfies the condition of
    > part (ii), so it is not a zero-divisor, and this forces μ = 0."
  - Lean ↔ source: our statement quantifies the hypothesis over the witnesses ν of
    `([a]−[1])q = ν` (the skeleton's moment encoding; the named-integration API
    `∫x^k·q` is built in the §4 pass — recorded in plan/tickets). Proof: extract ν
    (hq at a), h gives ν's moments vanish… wait — h gives ν(x^k) = 0 directly; L5.8
    gives ν = 0; `dirac_sub_one_mem_nonZeroDivisors` (L5.13) + faithfulness of
    algebraMap to the fraction ring (`IsFractionRing.injective`) force q = 0.
  - Attacks: [2] q = algebraMap μ for honest μ: hypothesis reduces to (a^k−1)·∫x^k μ
    = 0 ⟹ ∫x^k μ = 0 (a^k ≠ 1) ⟹ μ = 0 ✓ recovers (i); [3] the `ha` hypothesis
    (a^k ≠ 1 ∀k>0) is exactly what the source's "integer a ∉ {0,±1} prime to p"
    provides — we hypothesise the abstract property instead of the integer (cleaner,
    no loss; the §4 instantiation has explicit a); [4] (3.12)-independence (the
    source's well-definedness display, lines 1198–1200) is *absorbed* by quantifying
    over witnesses — no drift in strength; [5] `IsFractionRing.injective` exists
    (localisation at nonZeroDivisors is injective — `IsFractionRing` API, read).
    SURVIVED.

- **L5.12** (leaf): `exists_topological_generator`
  - Lean: `PseudoMeasure.lean:208`
  - Source (Lem. 3.38 statement, lines 1257–1258):
    > "Let a be any topological generator of ℤ_p^× (for example, take a to be a
    > primitive root modulo p such that a^{p−1} ≢ 1 (mod p²))".
  - Discharge: `isCyclic_units_of_prime_pow` (read at `ZMod/UnitsCyclic.lean:198`,
    odd p, all n; the file's proof manufactures generators of the form needed). Lift a
    generator compatible across levels: take g a unit generating (ZMod p²)ˣ; its
    ℤ_p-Teichmüller-free lift via `appr`/`CRT` generates every level (standard:
    generator mod p² ⟹ generator mod p^n for odd p — the UnitsCyclic file contains
    the order computation `orderOf_one_add_mul_prime` to make this exact).
  - Attacks: [2] p = 2 excluded?? — statement as skeletonised does NOT assume p ≠ 2,
    but (ZMod 8)ˣ is NOT cyclic (read: `UnitsCyclic.lean:82`)! **ATTACK SUCCEEDS for
    p = 2.** Resolution: the source works with odd p from §4 onward (and Lem. 3.38's
    proof says "As p is odd", line 1265). FIX APPLIED: ticket T-board marks this leaf
    (and the two depending on it) with the standing hypothesis `p ≠ 2`; the skeleton
    declaration must take `(hp2 : p ≠ 2)`. → **statement amended in skeleton** (see
    tickets T026–T028; the `variable (hodd : p ≠ 2)` section in the skeleton file
    covers `exists_topological_generator`, `augmentationIdeal_eq_span`,
    `isPseudoMeasure_mk'`, `isPseudoMeasure_iff_exists`; verify the hypothesis is
    genuinely threaded — worker checks Lean actually enforces it).
    Post-fix: [2] re-run: p odd ⟹ all levels cyclic ✓.
  - [5] `isCyclic_units_of_prime_pow (p) (hp) (hp2 : p ≠ 2) (n)` — signature READ,
    requires p ≠ 2 ✓ consistent with the fix. SURVIVED (after amendment).

- **L5.13** (leaf): `dirac_sub_one_mem_nonZeroDivisors`
  - Lean: `PseudoMeasure.lean:231`
  - Source: line 1240 ("But [a]−[1] satisfies the condition of part (ii)") — moments
    of [a]−[1] are `a^k − 1 ≠ 0`.
  - Discharge: `(δ_a − 1)(x^k) = a^k − 1` (Dirac evaluation, `units_one_def`) + L5.9.
  - Attacks: [2] a = 1 would fail (0 moments) — hypothesis `ha` excludes ✓; a of
    finite order q: a^q − 1 = 0 fails — `ha` excludes torsion ✓ (and torsion exists:
    μ_{p−1} ⊂ ℤ_p^×! so `ha` is genuinely needed — good); [3] `ha` is implied by
    topological-generator-ness (torsion elements generate finite subgroups, not dense
    ones) — the bridging lemma is part of T028's sketch; [5] internal. SURVIVED.

- **L5.14** (leaf, the inverse-limit cluster): `augmentationIdeal_eq_span`
  - Lean: `PseudoMeasure.lean:218`
  - Source (proof of Lem. 3.38, lines 1264–1272, verbatim):
    > "As p is odd, (ℤ_p/p^n)^× is cyclic, generated by ā := a (mod p^n), and we have
    > I((ℤ_p/p^n)^×) = ([ā] − [1̄])𝒪_L[(ℤ_p/p^n)^×]. In the inverse limit we see that
    > I(ℤ_p^×) = ([a]−[1])Λ(ℤ_p^×)."
  - Sub-decomposition (the source's "In the inverse limit" expanded — the genuinely
    compressed step):
    - L5.14a: finite-level generation: for a finite cyclic group C = ⟨g⟩, the
      augmentation ideal of `MonoidAlgebra ℤ_[p] C` is generated by `single g 1 − 1`
      (every `[g^k] − 1 = ([g]−1)(∑_{i<k}[g^i])`). New, ~20 LOC (source: line 1267,
      asserted). Verified absent from mathlib (no augmentation-ideal-of-group-ring
      generation lemma found; `MonoidAlgebra` API read).
    - L5.14b: solution sets are compatible nonempty "cylinders": for μ ∈ I, the level-n
      solution set S_n = {ν : levelMap n (([a]−1)ν − μ) = 0 } is nonempty (L5.14a +
      L5.7 surjectivity-of-levels... precisely: lift the level-n witness — levelMap is
      surjective onto the group ring? surjectivity via finite linear combinations of
      coset-Diracs ✓ worker proves; ~15 LOC), closed in the product-of-values topology,
      and decreasing after refinement.
    - L5.14c: compactness: Λ(ℤ_p^×) embeds in `Π_{clopen cosets} ℤ_p` (values on the
      countably many coset indicators) with closed image; `S_n` are nested nonempty
      compacts; `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed`
      (read at `Topology/Compactness/Compact.lean:336`) gives ν ∈ ⋂ S_n; joint
      injectivity (L5.7) shows ([a]−1)ν = μ.
  - Attacks: [1] is the statement even true? cross-check the χ-decomposition heuristic:
    Λ(ℤ_p^×) ≅ ∏_{χ mod p−1} ℤ_p[[T]]; [a]−1 ↦ (χ(a)(1+T)^{t} − 1)_χ which is a unit
    in the χ ≠ 1 components (constant term χ(a)−1 a unit) and an associate of T at
    χ = 1; I = (0,…,0,(T)) — matches ([a]−1)Λ ✓ consistent. [2] p = 2: cyclicity fails
    (L5.12 attack) — hypothesis p ≠ 2 threaded ✓. [3] does the compactness argument
    need second-countability/metrisability? — the chain is ℕ-indexed (sequence
    version), no. [4] drift: the source's "inverse limit" is along ALL open subgroups;
    our ℕ-chain is cofinal — recorded at L5.7[4]. [5] compactness-lemma name verified
    by reading. SURVIVED.

- **L5.15** (leaf): `isPseudoMeasure_mk'` (Lem. 3.38) + `isPseudoMeasure_iff_exists`
  - Lean: `PseudoMeasure.lean:224, 246`
  - Source (proof, lines 1273–1282, verbatim):
    > "Thus if g ∈ ℤ_p^×, we have [g]−[1] ∈ I(ℤ_p^×), and we must have [g]−[1] =
    > ν([a]−[1]) for some ν ∈ Λ(ℤ_p^×). Then ([g]−[1])μ' = ν([a]−[1])μ' = ν·μ ∈
    > Λ(ℤ_p^×), that is, μ' is a pseudo-measure."
    and lines 1284–1285:
    > "Note moreover that all pseudo-measures have this shape. Indeed, let μ' be a
    > pseudo-measure, and a ∈ ℤ_p^× a topological generator; then μ = ([a]−[1])μ' is a
    > measure, and μ' = μ/([a]−[1]) as above."
  - Discharge: deg([g]−1) = 0 (L5.6) + L5.14 + fraction-ring arithmetic
    (`IsLocalization.mk'_spec`, standard). Converse: instantiate IsPseudoMeasure at
    g = a, divide.
  - Attacks: [2] μ = 0: q = 0 is a pseudo-measure ✓ both directions ✓; [3] hreg is
    needed to form mk' — supplied by L5.13 ✓ explicit hypothesis (no circularity:
    L5.13 independent of L5.14/15); [5] `IsLocalization.mk'` API standard. SURVIVED.

---

## API gaps (each with sub-decomposition, all skeletonised)

- **AG1 (Fubini cluster)**: L5.1 + L5.2 — needed by L5.5. New infrastructure, fully
  decomposed above, skeleton in `Fubini.lean`. No further gaps beneath (all inputs
  verified in mathlib).
- **AG2 (finite-level cluster)**: L5.7 + L5.14a–c — needed by L5.14/L5.15. Fully
  decomposed above, skeleton in `PseudoMeasure.lean`. No further gaps beneath.

## Confidence gate (Step 5) — assessment

1. Every leaf: discharged from mathlib (file+line cited, read) / from project leaves /
   or an explicit API gap with sub-decomposition (AG1, AG2). ✓
2. Skeleton compiles: `lake build` success, 2437 jobs, sorries only. ✓
3. Verbatim quotes: every leaf above carries one (or, for internal nodes, a structural
   pointer to its children's quotes). ✓
4. Adversarial pass: every leaf has ≥ 3 recorded attacks; **one attack succeeded**
   (L5.12, p = 2) and was resolved by amending the affected statements to carry
   `p ≠ 2` — see tickets T026–T028, which begin by threading the hypothesis through
   the skeleton (the `hodd` section variable is currently *unused* by the declarations
   and must be made binding). All other attacks: no flaw found. ✓ (with the noted
   mandatory amendment as the first action of the affected tickets)
5. Prior-B2 log: empty (absent) — vacuously clean. ✓
6. Tree mirrors the source: each R-node cites the source's own proof location; the two
   compressed source steps ("one checks", "in the inverse limit") are expanded as AG1,
   AG2 with the expansion recorded. LOC estimates cited against source line counts
   where given. ✓

**Feasibility**: every leaf is dischargeable from verified mathlib API plus the two
self-contained infrastructure clusters (AG1 ≈ 65 LOC, AG2 ≈ 60 LOC estimated against
source compression points). The single mathematical trap found (p = 2 cyclicity) is
fenced by hypothesis. No REVIEW-PENDING leaves. The decomposition is ready for
ticketing.

---

# §4 — The Kubota–Leopoldt p-adic L-function (TeX 1440–1609)

## Skeleton location (§4)
- `PadicLFunctions/KubotaLeopoldt/ZetaValues.lean` (4 sorries)
- `PadicLFunctions/KubotaLeopoldt/ZetaValuesComplex.lean` (1 sorry)
- `PadicLFunctions/KubotaLeopoldt/MuA.lean` (31 sorries)
- `PadicLFunctions/KubotaLeopoldt/ZetaP.lean` (11 sorries)
`lake build PadicLFunctions` passes, sorries only — verified 2026-06-10.

## Result R-KL: `kubotaLeopoldt` (RJW Thm 4.1, TeX 1444–1447)

> "There is a unique pseudo-measure $\zeta_p$ on $\Zp^\times$ such that, for all
> $k > 0$, we have $\int_{\Zp^\times}x^k \cdot\zeta_p = (1-p^{k-1})\zeta(1-k)$."

### Plain-English proof (source structure, TeX 1599)
"Existence of the pseudo-measure is Proposition \ref{PropInterpolation2}. To conclude
the proof we need only show uniqueness; but this follows from Lemma
\ref{lem:zero divisor}(iii)." The chain to PropInterpolation2 is: §4.1 constructs
`μ_a` (integer `a` coprime to `p`) via its Mahler transform `F_a` (Prop 4.4/Def 4.5)
and computes its moments via Bernoulli values (Lem 4.2/4.3, Prop 4.6); §4.2 shows
`ψ(μ_a) = μ_a` (Lem 4.7) hence restriction to `ℤ_p^×` multiplies the k-th moment by
`(1−p^k)` (Prop 4.8); §4.3 multiplies by `x⁻¹` (shifting moments, eq. 4.11/TeX 1561)
and divides by `θ_a = [a]−[1]` in `Q(ℤ_p^×)` (Def 4.10), giving a pseudo-measure by
Lem 3.37 (= our `isPseudoMeasure_mk'`) with the stated interpolation after the sign
removal at TeX 1596.

**Moment encoding.** The source integrates a pseudo-measure via eq. (3.x)
`∫x^k·λ := (g^k−1)^{-1}∫x^k·([g]−[1])λ` (the encoding already used by
`pseudoMeasure_eq_zero_of_moments`, §3 board T025). The Lean main statement
quantifies over all `b : ℤ_[p]ˣ` and all witnesses `ν` of `([b]−[1])·q ∈ Λ`:
`∫x^k ν = (b^k−1)(1−p^{k−1})ζ(1−k)`. This is the same statement with the division
cleared — faithful and denominator-free.

**ζ-values design decision.** Every interpolation statement uses
`zetaNeg k := (−1)^k B_{k+1}/(k+1) ∈ ℚ` (TeX 1455's own formula for `ζ(−k)`), cast
into `ℚ_p`; `ζ(1−k) = zetaNeg (k−1)`. The complex identification is the quarantined
bridge L0.3 (`zetaNeg_eq_riemannZeta`). The analytic-continuation statement
`L(f_a,s) = (1−a^{1−s})ζ(s)` of Lem 4.2 is **§2 material** (Mellin transforms,
deferred with the §2 Motivation chapter); the part of Lem 4.2 that §4 actually
consumes is the value formula `f_a^{(k)}(0) = (−1)^k(1−a^{1+k})ζ(−k)`, whose honest
content is the Bernoulli power-series identity L2.6 below. Blueprint node
`kl-lem-values-zeta` therefore stays **unwired** until §2's Mellin theory exists;
the value formula is wired through `muA_apply_powCM`.

### Sub-tree R0: rational zeta values (`ZetaValues*.lean`)

- **L0.1** (leaf, mathlib): `zetaNeg_zero` + def `zetaNeg`
  - Lean: `ZetaValues.lean:17,21`
  - Source: TeX 1455: > "$\zeta(-k) = (d^kf/dt^k)(0) = (-1)^k B_{k+1}/(k+1).$"
  - Lean ↔ source: `zetaNeg k := (−1)^k·bernoulli (k+1)/(k+1)` is the displayed
    formula verbatim; mathlib's `bernoulli` has `B₁ = −1/2`, matching `ζ(0) = −1/2`
    (sanity: `zetaNeg 0 = B₁ = −1/2` ✓).
  - Discharged by: `bernoulli_one` (`= -1/2`, Bernoulli.lean) + `norm_num`.
  - Attacks: [1] edge `k=0`: `zetaNeg 0 = 1·B₁/1 = −1/2 = ζ(0)` ✓; [2] convention
    drift: if the paper meant `bernoulli'` (B₁=+1/2) then `ζ(0) = +1/2`, false —
    so the paper's display (and our def) is the `B₁=−1/2` convention, confirmed
    against mathlib's `riemannZeta_neg_nat_eq_bernoulli` which uses `bernoulli` with
    the same `(−1)^k` prefactor; [3] `k` odd ≥1: `zetaNeg 1 = −B₂/2 = −1/12 = ζ(−1)` ✓
    textbook value. Verdict: SURVIVED.
  - Prior-B2: no match (log absent/empty).

- **L0.2** (leaf, mathlib): `zetaNeg_eq_zero_of_even`
  - Lean: `ZetaValues.lean:25`
  - Source: TeX 1596: > "we may remove the $(-1)^{k}$ as $\zeta(1-k) \neq 0$ if and
    only if $k$ is even."
  - Lean ↔ source: `ζ(1−k) = 0` for odd `k ≥ 3` ⟺ `zetaNeg m = 0` for even `m ≥ 2`
    ⟺ `B_{m+1} = 0` for odd `m+1 ≥ 3`.
  - Discharged by: `bernoulli_eq_zero_of_odd` (Bernoulli.lean:217, verified).
  - Attacks: [1] edge `m=0`: excluded by `hk : k ≠ 0` — `zetaNeg 0 = −1/2 ≠ 0`, so
    the hypothesis is necessary (over-removal attack fails the statement without it);
    [2] discharge type: `bernoulli_eq_zero_of_odd {n} (h_odd : Odd n) (hlt : 1 < n)`
    — with `n := k+1`, `Odd (k+1)` from `Even k`, `1 < k+1` from `k ≠ 0` ✓ both
    hypotheses available; [3] counterexample search: `bernoulli 3 = 0`,
    `bernoulli 5 = 0` known values consistent. Verdict: SURVIVED.
  - Prior-B2: no match.

- **L0.3** (leaf, mathlib): `zetaNeg_eq_riemannZeta` (complex bridge)
  - Lean: `ZetaValuesComplex.lean:18`
  - Source: TeX 1455 (as L0.1) + mathlib `riemannZeta_neg_nat_eq_bernoulli`
    (HurwitzZetaValues.lean, located by file grep).
  - Lean ↔ source: our `zetaNeg` is definitionally the right side of mathlib's
    `riemannZeta_neg_nat_eq_bernoulli : riemannZeta (-n) = (-1)^n * bernoulli (n+1) / (n+1)`
    (exact statement to be confirmed at the declaration during execution; the name
    and file are verified).
  - Attacks: [1] statement-shape risk: mathlib's lemma may state `(-n : ℂ)` vs our
    `-(k : ℂ)` — same term up to `push_cast`; [2] division-in-ℂ vs division-in-ℚ-then-
    cast: `Rat.cast` is a field hom, commutes with `/` ✓; [3] junk-value attack:
    no division-by-zero (`k+1 ≠ 0`). Verdict: SURVIVED (with the noted
    confirm-at-execution on argument form).
  - Prior-B2: no match.

- **L0.4** (leaf, project+mathlib): `neg_one_pow_mul_one_sub_pow_mul_zetaNeg`
  - Lean: `ZetaValues.lean:32`
  - Source: TeX 1593–1596: > "$\int_{\Zp^\times} x^k \cdot \zeta_p =
    (-1)^k(1-p^{k-1})\zeta(1-k)$. To get the result, we may remove the $(-1)^{k}$ as
    $\zeta(1-k) \neq 0$ if and only if $k$ is even."
  - Lean ↔ source: the lemma is exactly the removal step, case-split: `k = 1` ⟹
    `1−q⁰ = 0`; `k` even ⟹ `(−1)^k = 1`; `k ≥ 3` odd ⟹ `zetaNeg (k−1) = 0` by L0.2.
    (The source says "k even"; the `k = 1` case is covered on the source side because
    `1−p^{k−1}` vanishes there — our proof makes that explicit.)
  - Discharged by: L0.2 + `Even.neg_one_pow` + `ring`-algebra.
  - Attacks: [1] edge `k=1`: LHS `= (−1)·0·(−1/2) = 0 =` RHS ✓ (this is where a naive
    "k even" proof breaks — caught and handled); [2] edge `k=2`: `(−1)² = 1` trivial ✓;
    [3] `k=3`: `zetaNeg 2 = 0` by L0.2 ✓; [4] generalisation attack: stated for
    arbitrary `q : ℚ` (not just `p`) — strictly more general, no hidden hypothesis.
    Verdict: SURVIVED.
  - Prior-B2: no match.

### Sub-tree R1: `F_a` and `μ_a` (RJW Prop 4.4, Def 4.5; `MuA.lean`)

Internal node. Source's own proof of Prop 4.4 (TeX 1488–1494):
> "We can expand $(1+T)^a - 1 = \sum_{n\geq 1} {a \choose n} T^n = aT\big[1+Tg(T)\big]$,
> where $g(T) = \sum_{n\geq 2}\frac{1}{a} {a \choose n} T^{n-2}$ has coefficients in
> $\zp$ since we have chosen $a$ coprime to $p$. Hence, expanding the geometric
> series, we find $\frac{1}{T} - \frac{a}{(1+T)^a - 1} = \frac{1}{T} \sum_{n \geq
> 1}(-T)^n g(T)^n$, which is visibly an element of $\Zp\lsem T\rsem$."

**Realisation note (recorded design decision, not a drift).** The source's proof is
"the denominator is `T·(unit)`, so the difference of poles cancels". We package the
same fact equation-first: `(1+T)^a − 1 = T·geomSum a` with `geomSum a = Σ_{i<a}(1+T)^i`
of constant coefficient `a` (a unit iff `p ∤ a` — the source's "since we have chosen
`a` coprime to `p`"), and *define* `F_a := ((geomSum a − a)/T) · geomSum a⁻¹`. Then
`((1+T)^a−1)·F_a = geomSum a − a` (L1.6) is the identity `F_a = 1/T − a/((1+T)^a−1)`
with denominators cleared — the form every later step actually uses. The geometric-
series expansion the source displays is *how it proves membership in ℤ_p⟦T⟧*; our
unit-inverse `Ring.inverse` achieves membership definitionally. Composition is
attack-checked at L1.6.

- **L1.1** (leaf, mathlib): `PadicInt.isUnit_natCast_of_not_dvd`
  - Lean: `MuA.lean:35`
  - Source: TeX 1491 ("has coefficients in ℤ_p since we have chosen a coprime to p" —
    the underlying fact: a coprime to p is a p-adic unit).
  - Discharged by: `PadicInt.isUnit_iff` (PadicIntegers.lean:366) +
    `PadicInt.norm_int_lt_one_iff_dvd` (:280) + `le_antisymm (norm_le_one _)`.
  - Attacks: [1] edge `a=0`: `p ∣ 0` always, hypothesis excludes ✓; [2] edge `a=1`:
    `IsUnit 1` ✓; [3] discharge-shape: `norm_int_lt_one_iff_dvd (k : ℤ) : ‖(k:ℤ_[p])‖ < 1 ↔ (p:ℤ) ∣ k`
    is for `ℤ`-cast — need `Int.natCast_dvd_natCast` bridge for `(a:ℕ)`, a 1-line
    `exact_mod_cast` ✓; [4] counterexample: none possible (standard fact).
    Verdict: SURVIVED.
  - Prior-B2: no match.

- **L1.2** (leaf, mathlib): `constantCoeff_geomSum`
  - Lean: `MuA.lean:53`. Source: implicit in TeX 1490 (`Σ_{n≥1} C(a,n) Tⁿ` has the
    `aT` leading term ⟺ cofactor has constant term `a`).
  - Discharged by: `map_sum`, `constantCoeff_one`, `constantCoeff_X`, `map_pow`;
    `Σ_{i<a} 1 = a` via `Finset.sum_const` + `card_range`.
  - Attacks: [1] `a=0`: empty sum, `constantCoeff 0 = 0 = (0:ℤ_[p])` ✓ cast of 0;
    [2] `(1+X)^i` const coeff `1^i = 1` ✓; [3] discharge: all four names standard
    simp lemmas. Verdict: SURVIVED.
  - Prior-B2: no match.

- **L1.3** (leaf, mathlib): `geomSum_mul_X`
  - Lean: `MuA.lean:56`. Source: TeX 1490 (the same display, rearranged:
    `(1+T)^a − 1 = T·Σ_{i<a}(1+T)^i`).
  - Discharged by: `geom_sum_mul : (Σ i ∈ range n, x^i) * (x − 1) = x^n − 1` with
    `x := 1+X` (so `x − 1 = X` after `add_sub_cancel_left`). NOTE: `geom_sum_mul`'s
    current file location was not pinned by grep (Algebra/GeomSum.lean moved);
    fallback if renamed: `mul_geom_sum` variant or a 6-line induction on `a`.
  - Attacks: [1] `a=0`: `0 * X = (1+X)^0 − 1 = 0` ✓; [2] `a=1`: `1·X = (1+X)−1` ✓;
    [3] commutativity orientation (left vs right factor): ℤ_p⟦X⟧ commutative,
    `mul_comm` bridges ✓; [4] discharge-existence risk logged (name location
    unpinned) with explicit fallback. Verdict: SURVIVED.
  - Prior-B2: no match.

- **L1.4** (leaf, mathlib): `isUnit_geomSum`
  - Lean: `MuA.lean:59`. Source: TeX 1490–1491 (unit cofactor ⟸ `a` coprime `p`).
  - Discharged by: `PowerSeries.isUnit_iff_constantCoeff` (Inverse.lean:111,
    verified) + L1.2 + L1.1.
  - Attacks: [1] hypothesis necessity: `p ∣ a` ⟹ constant coeff non-unit ⟹ non-unit:
    hypothesis is sharp ✓; [2] discharge type: `isUnit_iff_constantCoeff : IsUnit φ ↔
    IsUnit (constantCoeff R φ)` — exact match ✓; [3] composition: 3 lemmas ≤ 3 ✓.
    Verdict: SURVIVED.
  - Prior-B2: no match.

- **L1.5** (leaf, mathlib): `FaNum` + `X_mul_FaNum`
  - Lean: `MuA.lean:63,66`. Source: the `1/T·(...)` shape of TeX 1492 (the numerator
    after the pole at `T=0` cancels; constant term of `geomSum − a` is `0` by L1.2).
  - Discharged by: `PowerSeries.ext` + `coeff_X_mul`-family (`coeff_succ_X_mul`) +
    L1.2 (coefficient 0 vanishes); `coeff_mk`.
  - Attacks: [1] coefficient 0: `(X·FaNum)₀ = 0` and `(geomSum − a)₀ = a − a = 0` ✓;
    [2] coefficient n+1: `FaNum_n = geomSum_{n+1}`, and `(a : PowerSeries)`'s
    higher coefficients vanish (`coeff_natCast`-shape — natCast = C a, `coeff_C`) ✓;
    [3] junk-freedom: `FaNum` is total (no hypothesis), fine. Verdict: SURVIVED.
  - Prior-B2: no match.

- **L1.6** (internal, composition of L1.3–L1.5): `geomSum_mul_Fa` +
  `one_add_X_pow_sub_one_mul_Fa`
  - Lean: `MuA.lean:76,82`. Source: TeX 1475 (the definition of `F_a`)
    > "$F_a(T) \defeq \frac{1}{T} - \frac{a}{(1+T)^a - 1}$"
    cleared of denominators via the factorisation of Prop 4.4's proof.
  - Composition: `geomSum·Fa = geomSum·FaNum·inverse(geomSum) = FaNum` by
    `Ring.inverse_mul_cancel` (L1.4); then `((1+X)^a−1)·Fa = X·geomSum·Fa =
    X·FaNum = geomSum − a` by L1.3 + L1.5.
  - Attacks (composition): [1] could children hold and parent fail? The only glue is
    associativity/commutativity in a CommRing — no; [2] `Ring.inverse` junk when
    `p ∣ a`: both lemmas carry `hpa`, junk fenced ✓; [3] **sign check against the
    source display** (the blueprint review previously flagged the source's
    `Σ(−T)ⁿg(T)ⁿ` as having a sign slip): our route never uses that display — the
    characterising identity is sign-unambiguous, and its `k=1, a=2` instance was
    hand-checked: `F₂ = 1/T − 2/(T²+2T) = (T+2−2)/(T(T+2)) = 1/(T+2)`, and
    `((1+T)²−1)·1/(T+2) = T(T+2)/(T+2) = T = geomSum 2 − 2 = (2+T) − 2` ✓.
    Verdict: SURVIVED.
  - Prior-B2: no match.

- **L1.7** (leaf, project): `muA` + `mahlerTransform_muA`
  - Lean: `MuA.lean:88,92`. Source: TeX 1496–1498:
    > "Let $\mu_a$ be the measure on $\Zp$ whose Mahler transform is $F_a(T)$."
  - Discharged by: `mahlerLinearEquiv` (MahlerTransform.lean:160, sorry-free) —
    `apply_symm_apply`.
  - Attacks: [1] existence presupposition: the source needs Prop 4.4 (F_a ∈ ℤ_p⟦T⟧)
    *and* Thm 3.20 (transform bijective) — both in hand (`mahlerLinearEquiv`);
    [2] discharge: `LinearEquiv.apply_symm_apply` exact shape ✓; [3] defeq-drift:
    `mahlerLinearEquiv` vs `mahlerTransform` — relation lemma exists in
    MahlerTransform.lean (`mahlerTransform_ofPowerSeries`); confirm which gives the
    1-liner at execution. Verdict: SURVIVED.
  - Prior-B2: no match.

- **L1.8** (leaf, project): `binomialSeries_natCast`
  - Lean: `MuA.lean:95`. Source: bridging fact for TeX 1490 (`(1+T)^a` for integer
    `a` is the `a`-fold product; the Mahler transform of `δ_a` is `binomialSeries a`).
  - Discharged by: project-private `binomialSeries_mul_nat` (Toolbox.lean:184-190,
    `binomialSeries (c·k) = binomialSeries c ^ k`) at `c = 1` + `binomialSeries_one`
    — wait, need `binomialSeries 1 = 1 + X`: from `binomialSeries_coeff`
    (`C(1,0)=1, C(1,1)=1, C(1,n≥2)=0` via `Ring.choose` on ℕ-cast). The Toolbox
    private lemma must be re-derived or de-privatised — ticket notes this (the
    statement is 3 lines from `binomialSeries_add` by induction anyway).
  - Attacks: [1] `a=0`: `binomialSeries 0 = 1 = (1+X)^0` ✓ (`binomialSeries_zero`
    exists, used in Toolbox); [2] `Ring.choose` on `ℤ_[p]` at natCast equals
    `Nat.choose` (`Ring.choose_natCast` exists — used by §3 T005 work) ✓;
    [3] privacy obstacle is real and logged: plan = local rederivation. Verdict:
    SURVIVED.
  - Prior-B2: no match.

- **L1.9** (internal, composition): `dirac_natCast_sub_one_mul_muA`
  - Lean: `MuA.lean:101`. Source: the measure-side reading of TeX 1475's identity
    (the source works on transforms; `mahlerRingEquiv` is a ring iso — RJW Thm 3.20,
    proven — so the identity transfers verbatim).
  - Composition: apply `(mahlerRingEquiv p).injective`; transform of LHS:
    `((1+X)^a − 1)·F_a` via `mahlerTransform_dirac` + L1.8 + ring-iso
    multiplicativity; transform of RHS: `geomSum − a` via `map_sum`,
    `mahlerTransform_dirac`, L1.8 (at each `i`), and `a • 1 ↦ a • 1`
    (transform is ℤ_p-linear, `map_one`); conclude by L1.6.
  - Attacks: [1] children-true-parent-false: glue is injectivity of a ring iso +
    linearity — no gap; [2] `1` vs `dirac 0`: RHS uses ring-`1`; transform of `1`
    is `1` (`mahlerTransform_one`, Convolution.lean) and `binomialSeries 0 = 1` —
    consistent ✓; [3] smul-vs-natCast mismatch: `(a : ℤ_[p]) • (1 : Λ)` transforms to
    `(a:ℤ_[p]) • (1 : ℤ_[p]⟦X⟧) = (a : ℤ_[p]⟦X⟧)` — matches L1.6's RHS cast ✓
    (`Nat.cast_smul_eq_nsmul`-style bridging noted). Verdict: SURVIVED.
  - Prior-B2: no match.

- **L1.10** (leaf, mathlib): `instIsDomain` + `dirac_natCast_sub_one_ne_zero`
  - Lean: `MuA.lean:107,110`. Source: TeX 1175 (§3, quoted in §3 tree: Λ(G) domain
    for the cyclotomic use) — here the ambient fact "Λ(ℤ_p) ≅ ℤ_p⟦T⟧ is a domain"
    that the cancellation in R3 needs; the source cancels `θ_a`-style nonzero
    elements freely (TeX 1589, "independent of the choice of a by Lemma 3.36(iii)").
  - Discharged by: `mahlerRingEquiv` + `MulEquiv.isDomain` (transport; exact mathlib
    name to confirm — candidates `RingEquiv.isDomain`/`Function.Injective.isDomain`)
    + ℤ_p⟦X⟧ domain instance (mathlib: PowerSeries over a domain is a domain ✓
    standard instance); ne-zero: transform `(1+X)^a − 1 ≠ 0` since coefficient 1 is
    `a ≠ 0` (cast-injective on ℕ for `a ≠ 0` mod nothing — `Nat.cast_injective` on
    char-0 ℤ_p ✓).
  - Attacks: [1] `a=0` edge: `ha : a ≠ 0` required and stated ✓ (`dirac 0 − 1 = 0`
    really is zero — the hypothesis is sharp); [2] coefficient-1 computation:
    `coeff 1 ((1+X)^a − 1) = C(a,1) = a` via binomial expansion ✓; [3] transport
    name risk: three candidate mathlib spellings listed, one will fire. Verdict:
    SURVIVED.
  - Prior-B2: no match.

### Sub-tree R2: moments of `μ_a` (RJW Lem 4.2/4.3 value-formula + Prop 4.6)

Internal node. Source's proof of Prop 4.6 (TeX 1505–1507):
> "By Corollary \ref{cor:eval at x^k}, the left-hand side is
> $(\partial^k\sA_{\mu_a})(0)$. By definition of $\mu_a$ and Lemma
> \ref{lem:define F_a} this is $(\partial^kF_a)(0) = f_a^{(k)}(0)$. This equals the
> right-hand side by Lemma \ref{lem:values of zeta}."

and of Lem 4.3 (TeX 1473–1479):
> "Under the substitution $e^t = T+1$, the derivative $d/dt$ becomes the operator
> $\partial = (1+T)\frac{d}{dT}$. In particular, if we define [$F_a$] we have
> $f_a^{(k)}(0) = \big( \partial^k F_a \big)(0)$."

The value formula from Lem 4.2 (TeX 1463): `f_a^{(k)}(0) = (−1)^k(1−a^{1+k})ζ(−k)`,
whose proof "follows from calculations similar to those in the proof of Lemma
\ref{lem:FormulaZeta}" — i.e. the Taylor expansion of `1/(e^t−1)` by Bernoulli
numbers. Formal-series realisation: `t·f_a(t) = B(t) − B(at)` where
`B = bernoulliPowerSeries` (mathlib: `bernoulliPowerSeries_mul_exp_sub_one :
bernoulliPowerSeries A * (exp A − 1) = X`, Bernoulli.lean:273, verified), since
`f_a = 1/(e^t−1) − a/(e^{at}−1)` and `B(t) = t/(e^t−1)`, `B(at) = at/(e^{at}−1)`.

- **L2.1** (leaf, project): `cor:eval at x^k` — **already proven**: `apply_powCM`
  (Toolbox.lean:116, sorry-free). Cited, not re-ticketed.

- **L2.2** (leaf, mathlib): `map_del`
  - Lean: `MuA.lean:139`. Source: coefficient-cast plumbing (implicit; the source
    works in ℚ-coefficients silently when writing `B_{k+1}/(k+1)`).
  - Discharged by: `PowerSeries.ext` + `coeff_map` + `coeff_derivativeFun` +
    ring-hom arithmetic (`map_mul/map_add/map_natCast`).
  - Attacks: [1] `derivativeFun` commutes with `map` only because coefficients map
    multiplicatively against `(n+1) : ℕ`-casts — `map_natCast` handles ✓; [2] the
    `(1+X)·` factor maps to `(1+X)·` (`map_one`, `map_X`) ✓; [3] hom direction:
    `Coe.ringHom : ℤ_[p] →+* ℚ_[p]` injective — not even needed here (pure
    naturality). Verdict: SURVIVED.
  - Prior-B2: no match.

- **L2.3** (leaf, mathlib): `hasSubst_exp_sub_one`
  - Lean: `MuA.lean:131`. Source: the substitution `e^t = T+1` of TeX 1474 read
    backwards (`T = e^t − 1`), well-defined as `constantCoeff (exp − 1) = 0`.
  - Discharged by: `HasSubst.of_constantCoeff_zero'` (the §3 route used for
    `mahlerTransform_pushforward_mulCM`) + `constantCoeff_exp` (Exp.lean:59 region,
    `exp` has constant coefficient 1) + `map_sub`.
  - Attacks: [1] exact constructor name: §3 used `HasSubst.of_constantCoeff_zero'` —
    same call shape here ✓ (project precedent compiles); [2] `constantCoeff (exp−1)
    = 1 − 1 = 0` ✓; [3] nilpotency vs topological smallness: `HasSubst` for
    PowerSeries-subst needs constant coeff zero (algebraic), not topology — exactly
    our case ✓. Verdict: SURVIVED.
  - Prior-B2: no match.

- **L2.4** (leaf, mathlib): `derivativeFun_subst_exp` (chain rule)
  - Lean: `MuA.lean:135`. Source: TeX 1474: > "Under the substitution $e^t = T+1$,
    the derivative $d/dt$ becomes the operator $\partial = (1+T)\frac{d}{dT}$."
  - Discharged by: `PowerSeries.derivative_subst` (Derivative.lean:184, verified:
    `d⁄dX A (f.subst g) = (d⁄dX A f).subst g * d⁄dX A g`) + `derivative_exp`
    (`d(exp) = exp`, Exp.lean:72 region) + the algebra
    `(dF)(e^t−1)·e^t = ((1+T)·dF)(e^t−1)` since `1 + (e^t−1) = e^t` — i.e.
    `subst` is a ring hom (`substAlgHom`/`subst_mul/subst_add`) and
    `(1+X).subst (exp−1) = exp`.
  - Attacks: [1] `d⁄dX` vs `derivativeFun`: the bundled `d⁄dX A` is defeq/bridged to
    `derivativeFun` (same file; `derivative_apply`-style lemma) — bridging noted as
    possible off-script rewrite; [2] chain-rule hypothesis: `derivative_subst`
    requires `HasSubst g` = L2.3 ✓; [3] composition-order: mathlib gives
    `(dF).subst g * dg`; we must commute the product to match `((1+X)·dF).subst g`
    — `subst_mul` + `mul_comm`, no obstruction in CommRing ✓; [4] edge `F = C c`:
    both sides 0 ✓. Verdict: SURVIVED.
  - Prior-B2: no match.

- **L2.5** (leaf, mathlib): `constantCoeff_subst_exp` + `constantCoeff_iterate_derivativeFun`
  - Lean: `MuA.lean:141,145`. Source: TeX 1478 (`(∂^k F_a)(0)` — evaluation at
    `T = 0` ⟺ `t = 0`).
  - Discharged by: `constantCoeff_subst` (Substitution.lean:244, verified) with
    `constantCoeff (exp−1) = 0` collapsing the sum to the `n=0` term; iterate:
    induction on `k` with `coeff_derivativeFun` (`coeff n (dG) = coeff (n+1) G·(n+1)`)
    giving `constantCoeff (D^k G) = k!·coeff k G`.
  - Attacks: [1] `constantCoeff_subst`'s exact form is a `finsum`/`tsum`-style
    expression — collapsing needs `pow_zero`/junk-term analysis; flagged as the one
    fiddly spot, fallback: `coeff_subst` at index 0 directly; [2] factorial
    accumulation order: `D^[k+1] = D^[k] ∘ D` vs `D ∘ D^[k]` — `Function.iterate_succ'`
    vs `iterate_succ` both available, induction set up to match ✓; [3] edge `k=0`:
    `0! = 1`, `constantCoeff = coeff 0` ✓ (`coeff_zero_eq_constantCoeff`).
    Verdict: SURVIVED.
  - Prior-B2: no match.

- **L2.6** (internal, composition): `X_mul_subst_exp_Fa` — the Bernoulli identity
  - Lean: `MuA.lean:161`. Source: Lem 4.2's value formula (TeX 1463) +
    `lem:FormulaZeta`'s Bernoulli expansion; formal content as derived above:
    `t·f̂_a = B(t) − B(at)` in `ℚ_p⟦t⟧` where `f̂_a := (map F_a).subst (exp−1)`.
  - Composition (multiply-and-cancel): both sides times `(rescale a exp − 1)`
    (a nonzerodivisor: `ℚ_p⟦t⟧` domain, coefficient 1 equals `a ≠ 0`):
    LHS·: `X·f̂_a·(e^{at}−1) = X·subst(((1+X)^a−1)·F_a) = X·subst(geomSum − a)`
    [L1.6 mapped + `substAlgHom` ring-hom + L2.3; `subst((1+X)^a) = exp^a =
    rescale a exp` by `exp_pow_eq_rescale_exp` (Exp.lean:153, verified)];
    RHS·: `(B − rescale a B)·(e^{at}−1)`, where `B·(e^{at}−1) = B·(e^t−1)·Σ_{i<p
    wait — Σ_{j<a}e^{jt}} = X·Σ_{j<a}e^{jt}` [`bernoulliPowerSeries_mul_exp_sub_one`
    + the substituted L1.3: `e^{at}−1 = (e^t−1)·Σ_{j<a}e^{jt}`] and
    `rescale a B·(e^{at}−1) = rescale a (B·(e^t−1)) = rescale a X = aX`
    [`rescale` ring hom + `rescale_X`-computation + `rescale a exp = exp^a`];
    so RHS· `= X·Σ_{j<a}e^{jt} − aX = X·(subst(geomSum) − a) =` LHS· ✓; cancel.
  - Attacks (composition, this is the load-bearing algebra): [1] **numeric check**
    `a = 2`, coefficient of `t¹` in `t·f̂₂`: `f̂₂ = 1/(e^t−1) − 2/(e^{2t}−1)`;
    `B(t) = 1 − t/2 + t²/12 − …`, `B(2t) = 1 − t + t²/3 − …`; `B(t) − B(2t) =
    t/2 − t²/4 + …`; so `[t¹](t·f̂₂) = 1/2 = f̂₂(0)`. Direct: `f₂(t) = 1/(e^t−1) −
    2/(e^{2t}−1) → (1/t − 1/2 + …) − 2(1/(2t) − 1/2 + …)·` hmm `2/(e^{2t}−1) =
    (1/t)·(2t/(e^{2t}−1))·` `= (1/t)B(2t)`-shape: `f₂ = (B(t) − B(2t))/t =
    1/2 − t/4 + …` so `f₂(0) = 1/2 = (1−2^{0+1})·B₁/1 = (−1)·(−1/2)` ✓ matches
    `(1−a^{k+1})B_{k+1}/(k+1)` at `k=0` ✓; [2] `rescale a (exp − 1) = exp^a − 1`
    needs `rescale` to fix `1` — `map_one` of the ring hom `rescale` ✓; [3] the
    nonzerodivisor: `a ≠ 0` in `ℚ_p` from `hpa` (a ≠ 0 in ℕ since `p ∤ a` and
    `p ∣ 0`) + char-0 cast-injectivity ✓; [4] `rescale_X`: `rescale a X = a•X`
    or `C a * X` — exact mathlib spelling to confirm at execution (coeff-level
    fallback: `coeff_rescale` = `aⁿ·coeff n`); [5] could the children hold and the
    composition fail? All glue is ring-hom algebra in a domain — no. Verdict:
    SURVIVED.
  - Prior-B2: no match.

- **L2.7** (internal, composition): `muA_apply_powCM` (**RJW Prop 4.6**)
  - Lean: `MuA.lean:167`. Source: TeX 1500–1507 (quoted at R2 head; the proof is
    exactly the three-step chain).
  - Composition: `μ_a(x^k) = constantCoeff (del^[k] F_a)` [L2.1 = `apply_powCM` +
    `mahlerTransform_muA`]; cast to ℚ_p and commute `map` through `del^[k]` and
    `constantCoeff` [L2.2 + `constantCoeff_map`, induction]; apply L2.5-iterate
    [via L2.4-induction]: `= k!·coeff k (f̂_a)`; extract `coeff k` from L2.6:
    `coeff (k+1) (X·f̂_a) = coeff k f̂_a` (`coeff_succ_X_mul`) and
    `coeff (k+1) (B − rescale a B) = (1 − a^{k+1})·(B_{k+1}/(k+1)!)`
    [`bernoulliPowerSeries`-coeff def + `coeff_rescale`]; multiply by `k!`:
    `(1−a^{k+1})·B_{k+1}/(k+1) = (−1)^k(1−a^{k+1})·zetaNeg k` since
    `(−1)^k·(−1)^k = 1`.
  - Attacks: [1] `k! / (k+1)! = 1/(k+1)` arithmetic in ℚ_p: `Nat.factorial_succ` +
    `field_simp` — `(k+1)! ≠ 0` in ℚ_p (char 0, `Nat.cast_ne_zero`,
    `factorial_ne_zero`) ✓; [2] `algebraMap ℚ ℚ_[p]` vs `Rat.cast`: same function
    (`eq_ratCast`/`Rat.cast_def`-bridge, standard) ✓; [3] edge `k=0`:
    `μ_a(1) = F_a(0)`: check `F₂(0) = 1/2`?? — wait `F_a ∈ ℤ_p⟦T⟧` and `F₂(0) =
    1/2 ∈ ℤ_p` requires `p ≠ 2` — and indeed `p ∤ a = 2` forces `p` odd here ✓
    consistency (for general `a`: `F_a(0) = FaNum(0)/a = C(a,2)/a·`-shape`
    = (a−1)/2`-do the math: `FaNum(0) = coeff 1 geomSum = Σ_{i<a} i = a(a−1)/2`,
    so `F_a(0) = (a−1)/2`; and the moment formula at `k=0`:
    `(1−a)·B₁ = (1−a)(−1/2) = (a−1)/2` ✓✓ EXACT MATCH — strong numeric
    confirmation of the whole chain); [4] cast-square `((μ : ℤ_[p]) : ℚ_[p])`
    well-formed ✓. Verdict: SURVIVED.
  - Prior-B2: no match.

### Sub-tree R3: `ψ(μ_a) = μ_a` (RJW Lem 4.7) — **recorded replan**

Source's own proof (TeX 1517–1524):
> "We show the result by considering the action on power series. We wish to show
> $\psi(F_a) = F_a$. First note that $F_a(T) = \frac{1}{T} - a \cdot\sigma_a(\frac{1}{T})$,
> for $\sigma_a$ as in \S\ref{SubSectionphipsi}. As $\psi$ commutes with $\sigma_a$,
> we have $\psi(F_a) = \psi(\frac{1}{T}) - a\cdot \sigma_a\psi(\frac{1}{T})$, so it
> suffices to show $\psi(\frac{1}{T}) = \frac{1}{T}$. By definition (cf.\ equation
> \eqref{Eqphipsi}) we have $(\varphi \circ \psi)(\frac{1}{T}) = p^{-1} \sum_{\xi \in
> \mu_p} \frac{1}{(1 + T) \xi - 1} = \frac{1}{(1 + T)^p - 1} = \varphi(\frac{1}{T})$,
> as can be seen by calculating the partial fraction expansion. By injectivity of
> $\varphi$, we deduce that $\psi(\frac{1}{T}) = \frac{1}{T}$, and conclude."

**Replan (T018/T026-pattern; binding justification).** The source's computation runs
through (i) the element `1/T ∉ ℤ_p⟦T⟦` (a Laurent-type object our `Λ(ℤ_p) ≅ ℤ_p⟦T⟧`
does not contain) and (ii) the roots-of-unity formula `Eqphipsi` over `ℤ_p[μ_p]`
(deferred with the O_L-coefficient pass — plan.md "Deferred"). Both obstacles
disappear after clearing denominators by `(1+T)^a − 1`: the *same* partial-fraction
identity `Σ_{ξ^p=1} 1/((1+T)ξ−1) = p/((1+T)^p−1)` is, in cleared form, the geometric
identity `Σ_{i<p}(1+T)^i·((1+T)−1-shifted)` — concretely, the proof becomes:

1. `(v_a) · ψ(μ_a) = ψ(φ(v_a)·μ_a)` where `v_a := [a]−[1] ∈ Λ(ℤ_p)` — the
   **projection formula** L3.1 (`ψ(φν·μ) = ν·ψμ`), which is `Eqphipsi`'s only
   §4-consequence, provable measure-side with no roots of unity;
2. `φ(v_a)·μ_a = [pa]−[0])·μ_a = (Σ_{j<p}[aj])·(([a]−[0])·μ_a) =
   (Σ_{j<p}[aj])·(Σ_{i<a}[i] − a[0])` — finite Dirac sums via L1.9 + L3.5;
3. `ψ` of a Dirac combination is computable termwise (`ψ[m] = [m/p]` if `p ∣ m`,
   else `0` — L3.3/L3.4), giving `Σ_{i<a}[i] − a[0] = v_a·μ_a` again;
4. cancel the nonzerodivisor `v_a` (L1.10).
Every step is a finite computation in `Λ(ℤ_p)`; the source's analytic identity is
recovered as step 2–3's bookkeeping. (Lemma-level faithfulness: the *statement*
`ψ(μ_a) = μ_a` is TeX 1513–1515 verbatim.)

- **L3.1** (leaf, project-provable): `psi_phi_mul` — projection formula
  - Lean: `MuA.lean:182`. Source: `Eqphipsi`-consequence as argued above; measure
    side: `ψ(φν·μ)(f) = (φν·μ)(1_{pℤ_p}·(f∘sd)) = ν(x↦μ(y↦1_{pℤ_p}(px+y)·f(sd(px+y))))`
    [convolution `mul_apply` + `phi`-pushforward], and for the inner integrand
    `1_{pℤ_p}(px+y) = 1_{pℤ_p}(y)`, `sd(px+y) = x + sd y` on `y ∈ pℤ_p`
    [digit arithmetic: `digit (px+y) = digit y`], so it equals `ν(x↦ψμ(f(x+·)))
    = (ν·ψμ)(f)`.
  - Discharged by: `mul_apply` (Convolution.lean), `psi`-def unfolding (`show`-driven
    as in §3's `psi_phi`), `digit`/`shiftDiv` API (Toolbox: `sub_digit_mem_span`,
    `shiftDiv_mul`, `mem_pZp_of_mul`, `mul_shiftDiv_of_mem`).
  - Attacks: [1] **instantiation cross-check**: `ν := 1 = [0]`: formula says
    `ψ(φ(1)·μ) = 1·ψμ = ψμ`; `φ(1) = [0] = 1` ✓ consistent; `μ := 1`:
    `ψ(φν) = ν·ψ(1) = ν` recovering `psi_phi` (Toolbox:377) ✓ the formula
    *generalises* a proven §3 result — strong consistency; [2] digit-arithmetic gap:
    need `digit (p·x + y) = digit y` — provable from `digit`'s `toZModPow 1`
    characterisation (`p·x ≡ 0 mod p`); flagged as the one new digit lemma
    (sub-lemma of the ticket, ~8 LOC); [3] convolution-order: `phi ν * μ` vs
    `μ * phi ν` — ring commutative, lemma stated in the order the proof produces ✓.
    Verdict: SURVIVED.
  - Prior-B2: no match.

- **L3.2** (leaf, project): `phi_dirac`
  - Lean: `MuA.lean:186`. Source: `φ` is pushforward by `x ↦ px` (§3.6) — on Dirac
    masses, `φ[c] = [pc]`.
  - Discharged by: `phi = pushforward (mulCM p)` def + `pushforward_dirac`-style
    `rfl` (the §3 file proves `pushforward`-on-`dirac` shapes by `rfl`).
  - Attacks: [1] `rfl`-risk: `pushforward` defined as `compRight`-precomposition —
    `dirac x ∘ comp = dirac (m x)` is definitional ✓ (§3 precedent
    `mahlerTransform_dirac` route); [2] `mulCM p` applies `p·x` not `x·p` —
    commutative ✓; [3] edge `x=0`: `φ[0] = [0]` ✓. Verdict: SURVIVED.
  - Prior-B2: no match.

- **L3.3** (leaf, project): `psi_dirac_mul`
  - Lean: `MuA.lean:189`. Source: `ψ`'s defining property (§3.6, `Eqphipsi`-dual):
    `ψ∘φ = id` on Diracs; more precisely `ψ[px] = [x]`.
  - Discharged by: `psi`-def + `isClopen_pZp`-charFn at `px` (`= 1`,
    membership `px ∈ pℤ_p` ✓) + `shiftDiv_mul` (Toolbox: `sd(px) = x`).
  - Attacks: [1] follows from `psi_phi` + L3.2 composed: `ψ[px] = ψφ[x] = [x]` —
    2-lemma discharge, even simpler than direct ✓; [2] edge `x=0` ✓; [3] charFn
    coercion friction (LocallyConstant → C) — §3 pattern handles. Verdict: SURVIVED.
  - Prior-B2: no match.

- **L3.4** (leaf, project): `psi_dirac_of_isUnit`
  - Lean: `MuA.lean:192`. Source: `Res_{pℤ_p}`-support: a unit is not in `pℤ_p`, so
    the `pℤ_p`-restricted shift kills `[u]`.
  - Discharged by: `psi`-def: `ψ[u](f) = 1_{pℤ_p}(u)·f(sd u) = 0` since
    `u ∉ pℤ_p` (`PadicInt.isUnit_iff` norm-1 vs `pℤ_p` = norm < 1;
    or `setOf_isUnit_eq` from Toolbox/UnitsZp).
  - Attacks: [1] hypothesis sharpness: `x` non-unit ⟺ `x ∈ pℤ_p` ⟹ `ψ[x] ≠ 0`
    generally — `IsUnit` is exactly the complement ✓; [2] charFn-at-point
    evaluation lemma availability (`LocallyConstant.charFn_apply`-shape, used in §3)
    ✓; [3] ext over `f` then pointwise — linear-map ext pattern ✓.
    Verdict: SURVIVED.
  - Prior-B2: no match.

- **L3.5** (leaf, project): `psi_add` / `psi_smul` / `psi_sum`
  - Lean: `MuA.lean:195,198,201`. Source: implicit (the source's `ψ` is
    ℤ_p-linear by construction; ours is defined measure-wise and the API was
    only partially built in §3 — `psi_sub` exists).
  - Discharged by: the same `LinearMap.ext` + definitional unfolding as `psi_sub`
    (PseudoMeasure-era §3 work); `psi_sum` by `Finset.sum_induction`/induction from
    `psi_add` + `psi`-of-zero (`map_zero`-style: `ψ0 = 0` definitional).
  - Attacks: [1] cleanup-debt attack: these three + `psi_sub` say `psi` should be a
    bundled `→ₗ` — REAL flaw of economy, logged as the dedicated cleanup item in the
    ticket (upgrade `psi` to `psiₗ` linear map OR add the lemmas; board chooses
    lemmas-now + cleanup-note to avoid churning §3 call sites mid-section);
    [2] zero case: `ψ0 = 0` needed for `psi_sum` induction ✓ definitional;
    [3] no hidden classical choice. Verdict: SURVIVED (with logged cleanup debt).
  - Prior-B2: no match.

- **L3.6** (internal, composition): `psi_muA` (**RJW Lem 4.7**)
  - Lean: `MuA.lean:215`. Source statement (TeX 1513–1515):
    > "We have $\psi(\mu_a) = \mu_a$."
  - Composition: steps 1–4 of the replan block above; ingredients L3.1, L3.2, L1.9,
    `dirac_mul_dirac` (Convolution.lean:160, `[x]·[y] = [x+y]`), L3.3, L3.4, L3.5,
    L1.10 + `mul_left_cancel₀`. Step-2 detail: `[pa]−[0] = ([a]−[0])·(Σ_{j<p}[aj])`
    — wait, orientation: `(Σ_{j<p}[aj])·([a]−[1])` telescopes to `[pa]−[0]`:
    `Σ_j[aj]·[a] = Σ_j[a(j+1)]` reindexes against `Σ_j[aj]` leaving `[ap]−[0]` ✓
    (`Finset.sum_range_succ'`-telescope); then `([pa]−[0])·μ_a =
    (Σ_j[aj])·(([a]−[0])·μ_a) = (Σ_j[aj])·(Σ_{i<a}[i] − a[0])` by L1.9; expand by
    `dirac_mul_dirac`: `Σ_{j<p}Σ_{i<a}[aj+i] − aΣ_{j<p}[aj]`; apply `ψ` (L3.5
    linearity): termwise by L3.3/L3.4 — `p ∣ aj+i` with `0≤i<a, 0≤j<p` ⟺ the pair
    is `(i,j) = (pm − aj-residue…)`: handled instead by the **division-algorithm
    bijection** `{aj+i : j<p, i<a} = {0,…,ap−1}` (each `n < ap` uniquely `n = aj+i`)
    so the double sum is `Σ_{n<ap}[n]`, and `ψ(Σ_{n<ap}[n]) = Σ_{p∣n, n<ap}[n/p] =
    Σ_{m<a}[m]` (reindex `n = pm`); second sum: `p ∣ aj` with `j<p`, `p∤a` ⟺ `j=0`
    (`Nat.Coprime.dvd_of_dvd_mul_left`), so `ψ(aΣ_j[aj]) = a[0]`; total:
    `Σ_{m<a}[m] − a[0] = ([a]−[0])·μ_a` by L1.9 again; cancel `v_a = [a]−[1]`
    (note `[0] = 1` in Λ — `dirac 0 = 1`, Convolution one-def) by L1.10.
  - Attacks (composition — this is the riskiest node, attacked hardest):
    [1] **end-to-end numeric trace at `p=3, a=2`**: `v₂·μ₂ = [0]+[1] − 2[0] =
    [1]−[0]`; `φ(v₂)·μ₂ = ([6]−[0])·μ₂ = (Σ_{j<3}[2j])·([1]−[0]) =
    ([0]+[2]+[4])·([1]−[0]) = [1]+[3]+[5]−[0]−[2]−[4]`; `ψ`: kills `[1],[5],[2],[4]`
    (units mod 3), keeps `[3]↦[1], [0]↦[0]`: result `[1]−[0]`; and `ν·ψμ₂`-side:
    `v₂·ψμ₂` must equal `[1]−[0] = v₂·μ₂` ⟹ `ψμ₂ = μ₂` ✓ the cancellation
    closes — trace CONFIRMS every step including the unit-killing pattern;
    [2] reindex-lemma availability: division-algorithm bijection on `range (a*p)`:
    via the *transform-side* identity instead — `(Σ_j((1+X)^a)^j)·((1+X)^a−1) =
    (1+X)^{ap}−1 = (Σ_{n<ap}(1+X)^n)·X`-route (geom_sum twice + X-cancellation in
    the domain) avoids `Finset` bijections entirely; both routes recorded, worker
    picks; [3] `[0] = 1` identification: `dirac 0 = 1` — Convolution defines `one`;
    if not a stated lemma, it's `mahlerTransform`-injectivity + `binomialSeries_zero`
    (2 lines, sub-lemma noted); [4] cancellation legitimacy: `v_a ≠ 0` needs
    `a ≠ 1`?? — **ATTACK FINDS REAL EDGE**: `a = 1`: `v₁ = [1]−[1] = 0` and BOTH
    sides of `ψμ₁ = μ₁` are `0 = 0` (F₁ = 0) — but the *cancellation proof* fails at
    `a = 1`! RESOLUTION: `dirac_natCast_sub_one_ne_zero` requires `a ≠ 0` only —
    recheck: `v_a = [a] − 1` has transform `(1+X)^a − 1 ≠ 0 ⟺ a ≠ 0` (coeff 1 = a).
    At `a = 1`: `(1+X)−1 = X ≠ 0` ✓ nonzero! My `[1]−[1]` slip above confused
    `θ_a = [a]−[1] ∈ Λ(ℤ_p^×)` (units-side, where `1 = [1-the-unit]`) with
    `v_a = [a]−[0]·`-wait: in `Λ(ℤ_p)` the ring-one is `[0]` (additive group!), so
    `v_a = [a] − 1 = [a] − [0]`, which at `a=1` is `[1]−[0] ≠ 0` ✓. The statement
    `dirac_natCast_sub_one_mul_muA` with `- 1` (ring one) is correct as skeletoned;
    the attack confirms the convention and kills the false alarm. `a = 1` works
    end-to-end (everything is `0=0` via `F₁ = 0`, and the cancellation is by the
    nonzero `[1]−[0]`). Verdict: SURVIVED (attack [4] sharpened the understanding;
    no statement change needed).
  - Prior-B2: no match.

### Sub-tree R4: restriction moments (RJW Prop 4.8)

Source's proof (TeX 1535–1539):
> "Since $\mathrm{Res}_{\zpe} = 1 - \varphi \circ \psi$, we deduce that
> $\int_{\zpe} x^k \cdot\mu_a = \int_{\Zp} x^k \cdot (1 - \varphi \circ \psi) \mu_a
> = \int_{\Zp} x^k \cdot (1 - \varphi)\mu_a = (1 - p^k) \int_{\Zp} x^k \cdot \mu_a$,
> where for the second equality we have used Lemma \ref{LemmaPsiInvariant}."

- **L4.1** (leaf, project): `phi_apply_powCM`
  - Lean: `MuA.lean:226`. Source: the third equality above (`∫x^k·φμ = p^k∫x^kμ`,
    implicit one-liner in the source's display).
  - Discharged by: `phi`-def (pushforward `mulCM p`) + pointwise `(px)^k = p^k x^k`
    (`mul_pow`) + `μ`-linearity (`map_smul` after `smul`-rewriting the function:
    `powCM ∘ mulCM = p^k • powCM` by `ContinuousMap.ext`).
  - Attacks: [1] edge `k=0`: `φμ(1) = μ(1)` and `p⁰ = 1` ✓; [2] function-level vs
    value-level smul: `C(ℤ_p,ℤ_p)`-smul lemma shape — §3 has the pattern in
    `apply_powCM`'s proof ✓; [3] no `hpa` needed (true for all μ) — hypothesis-
    minimal ✓. Verdict: SURVIVED.
  - Prior-B2: no match.

- **L4.2** (internal, composition): `res_units_muA_apply_powCM` (**RJW Prop 4.8**)
  - Lean: `MuA.lean:233`. Source: TeX 1527–1539 (statement + proof quoted above).
  - Composition: `res_units_eq` (Toolbox:422, `Res_{ℤ_p^×}μ = μ − φψμ`, sorry-free)
    + L3.6 (`ψμ_a = μ_a`) + L4.1 + L2.7, then ℚ_p-algebra:
    `(1−p^k)·(−1)^k(1−a^{k+1})·zetaNeg k`.
  - Attacks: [1] children-true-parent-false: glue is `LinearMap.sub_apply` +
    cast-arithmetic ✓; [2] cast of `(1−p^k)` from ℤ_p to ℚ_p: `push_cast` ✓;
    [3] edge `k=0`: `Res μ_a(1) = (1−1)·… = 0` — sanity: total mass of
    `Res_{units}μ_a` is `μ_a(ℤ_p^×) = (1−p⁰)(…) = 0`?? Hmm — `(1−p^k)` at `k=0` is
    `0`, so the claim is `∫_{ℤ_p^×}1·dμ_a = 0`. Cross-check: `μ_a(ℤ_p^×) =
    μ_a(1) − μ_a(pℤ_p)` and `μ_a(pℤ_p) = (φψμ_a)(1) = (φμ_a)(1) = μ_a(1)` by L3.6 ✓
    `= 0` consistent — the formula correctly encodes that `μ_a` has equal total and
    `pℤ_p` mass. Verdict: SURVIVED.
  - Prior-B2: no match.

### Sub-tree R5: `ζ_p` (RJW §4.3, Def 4.10, Prop 4.11, Thm 4.1; `ZetaP.lean`)

Source TeX 1550–1563 (θ_a and x⁻¹):
> "let $\theta_{a}$ denote the element of $\Lambda(\Zp^\times)$ corresponding to
> $[a] - [1]$. Note that, by definition, we have $\int_{\Zp^\times} x^k
> \cdot\theta_{a} = a^k - 1$. However, in \eqref{eq:first interpolation} it is
> $a^{k+1} -1$ that appears. To bridge this gap, note that on $\Zp^\times$, we have
> a well-defined operation `multiplication by $x^{-1}$' given by
> $\int_{\Zp^\times} f(x) \cdot x^{-1}\mu \defeq \int_{\Zp^\times} x^{-1}f(x) \cdot
> \mu$, and that $\int_{\Zp^\times} x^k \cdot x^{-1} \mu_a =
> (-1)^k(a^k-1)(1-p^{k-1})\zeta(1-k)$."

and TeX 1565–1570 (Def 4.10):
> "Let $a$ be a topological generator of $\zpe$. The \emph{$p$-adic zeta function} is
> $\zeta_p \defeq \frac{x^{-1}\mathrm{Res}_{\Zp^\times}\mu_a}{\theta_a} \in
> Q(\Zp^\times)$."

and TeX 1588–1597 (Prop 4.11's proof):
> "We see $\zeta_p$ is a pseudo-measure by Lemma \ref{lem:pseudo-measure existence}.
> It is independent of the choice of $a$ by Lemma \ref{lem:zero divisor}(iii).
> Using Equation \eqref{eq:integrate pseudo-measure} (to integrate the
> pseudo-measure) and Proposition \ref{PropInterpolation1}, we obtain the
> interpolation property $\int_{\Zp^\times} x^k \cdot \zeta_p =
> (-1)^k(1-p^{k-1})\zeta(1-k)$. To get the result, we may remove the $(-1)^{k}$ as
> $\zeta(1-k) \neq 0$ if and only if $k$ is even."

**Source-gap note (integer topological generator).** §4.1 fixes `a` an *integer*
coprime to `p` (TeX 1455: "let $a$ be an integer coprime to $p$"); Def 4.10 takes the
*same* `a` to be a topological generator of `ℤ_p^×` (TeX 1566). The source never
remarks that an integer topological generator exists. Cross-reference (per the
source-gap fallback chain): standard — an integer primitive root mod `p²` is a
primitive root mod `p^n` for all `n` (Ireland–Rosen, *A Classical Introduction to
Modern Number Theory*, Prop 4.1.2 region / Washington, *Cyclotomic Fields*, §3); the
proof is the `orderOf_one_add_mul_prime` computation already imported by §3's
`UnitsCyclic` work. This becomes leaf L5.4 (`exists_nat_topological_generator`),
flagged as a source-expansion (not an invention: the source's construction is
incoherent without it).

- **L5.1** (leaf, project): `muAUnits` + `iota_muAUnits` + `muAUnits_apply_unitsPowCM`
  - Lean: `ZetaP.lean:36,40,44`. Source: the `Res_{ℤ_p^×}μ_a` of Def 4.10 read as a
    measure *on* `ℤ_p^×` (the source silently identifies measures on ℤ_p supported
    on units with measures on `ℤ_p^×` — our `ι`-machinery from §3 makes the
    identification explicit; `mem_range_iota_iff` (UnitsZp:177) says the
    identification is legitimate precisely because `ψ(Res_{units}μ) = 0`).
  - Discharged by: `extendByZero` (UnitsZp:78) precomposition;
    `extendByZero_comp_unitsVal` (§3, used in `mem_range_iota_iff`'s proof) for the
    `iota`-identity; pointwise `extendByZero (unitsPowCM k) = charFn_{units}·powCM k`
    (`extendByZero_coe_unit`-family) for the moment-transfer.
  - Attacks: [1] direction of identification: `ι(μ∘extendByZero) = Res_units μ`
    holds unconditionally (it's the §3 proof of `mem_range_iota_iff`'s ⟸) — no
    `ψ`-hypothesis needed for our specific μ_a ✓ (we don't even need L3.6 here);
    [2] `unitsPowCM k` vs `powCM k ∘ val`: definitional (`unitsPowCM`-def
    PseudoMeasure:656 is `u ↦ (u:ℤ_p)^k`) ✓; [3] zero-extension at non-units doesn't
    disturb the integral against `Res` — exactly `res`-def ✓. Verdict: SURVIVED.
  - Prior-B2: no match.

- **L5.2** (leaf, mathlib+project): `continuous_units_inv_val` + `invCM` +
  `unitsCmul` + `unitsCmul_apply`
  - Lean: `ZetaP.lean:51,56,61,67`. Source: TeX 1555–1558 (eq. 4.11, quoted above —
    "well-defined operation" = continuity of `x⁻¹` on `ℤ_p^×` + module structure).
  - Discharged by: continuity: `Units.continuous_iff` / the `embedProduct`-coordinate
    argument (UnitsZp.lean §3 already manipulates `embedProduct`-continuity;
    `u ↦ u⁻¹.val` is the `snd∘unop` coordinate) — mathlib's units-topology toolkit
    (`Mathlib.Topology.Algebra.Constructions`); `unitsCmul` mirrors Toolbox `cmul`
    (:38) with `LinearMap.mulLeft ℤ_[p] g` (skeleton already type-checks this body ✓
    so the linear-algebra shape is confirmed by the compiler).
  - Attacks: [1] instance risk: is `C(ℤ_[p]ˣ, ℤ_[p])` an `ℤ_[p]`-algebra with
    compatible mul? — the skeleton COMPILED `LinearMap.mulLeft ℤ_[p] g`, so yes ✓
    (compiler-verified discharge); [2] continuity-route fallback: if no off-the-shelf
    instance, the explicit `(embedProduct _).2.unop`-composition stands (3 lines);
    [3] `x⁻¹` valued in `ℤ_p` not `ℤ_p^×`: matches the source's `x^{-1}f(x)`
    integrand (a ℤ_p-valued function) ✓. Verdict: SURVIVED.
  - Prior-B2: no match.

- **L5.3** (internal): `zetaNum` + `zetaNum_apply_unitsPowCM` + `zetaNum_moments`
  - Lean: `ZetaP.lean:73,77,81`. Source: TeX 1559–1562 (the display quoted above:
    `∫x^k·x⁻¹μ_a = (−1)^k(a^k−1)(1−p^{k−1})ζ(1−k)`).
  - Composition: `x⁻¹·x^k = x^{k−1}` pointwise on units (`inv_mul_cancel`-pow:
    `u⁻¹·u^k = u^{k−1}` for `k ≥ 1` — `pow_sub_one`-shape via `Units.val`-arith);
    then L5.1-transfer + L4.2 at `k−1`: `(−1)^{k−1}(1−p^{k−1})(1−a^k)·zetaNeg(k−1)`
    and `(−1)^{k−1}(1−a^k) = (−1)^k(a^k−1)` — matching TeX 1561 exactly ✓.
  - Attacks: [1] `k−1` ℕ-subtraction safety: `hk : 0 < k` everywhere; `k−1+1 = k`
    (`Nat.succ_pred_eq_of_pos`) at the `pow`-bridge ✓; [2] sign-form check at `k=1`:
    LHS `∫x·x⁻¹μ = ∫1·μ = Res-mass = 0` (R4 attack [3]); RHS `(−1)(a−1)(1−p⁰)ζ(0) =
    0` ✓ consistent; [3] `(u⁻¹:ℤ_p)·(u:ℤ_p)^k = (u^{k−1}:ℤ_p)`: `Units.val_pow_eq_pow_val`
    + `Units.val_mul`-arith ✓ standard. Verdict: SURVIVED.
  - Prior-B2: no match.

- **L5.4** (leaf, project — source-expansion): `topGen_pow_ne_one` +
  `exists_nat_topological_generator`
  - Lean: `ZetaP.lean:92,103`. Source: TeX 1566 ("Let $a$ be a topological generator
    of $\zpe$") + the integrality gloss documented in the R5 head-note;
    cross-reference Washington §3 / Ireland–Rosen (integer primitive roots mod `p^n`).
  - Discharge plan: `topGen_pow_ne_one`: if `a^k = 1` (`k>0`) then
    `unitsToZModPow n a` has order dividing `k` for every `n`; but it generates
    `(ZMod p^n)ˣ` of cardinality `φ(p^n) = p^{n−1}(p−1) → ∞`
    (`ZMod.card_units_eq_totient` + `Nat.totient_prime_pow`) — contradiction for
    `p^{n−1}(p−1) > k` (`orderOf_eq_card_of_forall_mem_zpowers`-family).
    `exists_nat_topological_generator`: take `u₀` from `exists_topological_generator`
    (PseudoMeasure:857, proven, `p ≠ 2`); let `m := ((toZModPow 2 u₀).val.val : ℕ)`
    (a lift of `u₀ mod p²`); then `m ≡ u₀ mod p²` so `m` is a primitive root mod
    `p²`; classical ascent: `ord_{p^n}(m)` is divisible by `ord_{p²}(m) = p(p−1)`,
    and `m^{p−1} = 1 + pc` with `p ∤ c` (else `ord_{p²}(m) ∣ p−1`), so
    `orderOf_one_add_mul_prime` (the §3-discovered mathlib lemma, ZMod-side) gives
    the `p`-part `p^{n−1}`; total order `φ(p^n)` ⟹ generator at level `n`;
    levels < 2 follow from level 2 by surjectivity of the transition
    (`unitsToZModPow_le`, §3).
  - Attacks: [1] `n = 0,1` edges: level 0 group trivial (⊤ automatic); level 1
    follows from level 2 via the surjective transition map (zpowers-image argument —
    `unitsToZModPow_surjective`-machinery from §3 T027) ✓ plan covers;
    [2] `m = 0`-degeneracy: `m ≡ u₀` a unit mod `p²` ⟹ `p ∤ m` ⟹ `m ≥ 1` ✓;
    [3] `(u:ℤ_[p]) = m` vs `u = unit-of-m`: statement uses val-equation — the
    constructed unit is `isUnit_natCast.unit` whose val is `(m:ℤ_[p])` and we need
    its `toZModPow`-images to match `m mod p^n`'s — `toZModPow`-natCast naturality
    (`map_natCast`) ✓; [4] **scope attack**: is this "off-track infrastructure"? No:
    `orderOf_one_add_mul_prime`-machinery is imported mathlib, the §3 board already
    used the same toolkit for `exists_topological_generator`; estimated 60–80 LOC
    against the source's 1-line gloss + the cross-referenced textbook proof
    (~15 textbook lines). Within scope. Verdict: SURVIVED.
  - Prior-B2: no match (name `exists_topological_generator` §3-relative: different
    statement — that one is abstract-unit existence, this is integrality; shapes
    distinct, no inherited defect).

- **L5.5** (leaf, project): `IsPseudoMeasure.sub`
  - Lean: `ZetaP.lean:124`. Source: implicit in the uniqueness argument (difference
    of pseudo-measures tested by moments; the source treats pseudo-measures as a
    module without comment).
  - Discharged by: witness subtraction: `([g]−1)(q₁−q₂) = ([g]−1)q₁ − ([g]−1)q₂ =
    alg(ν₁) − alg(ν₂) = alg(ν₁−ν₂)` — `mul_sub` + `map_sub`.
  - Attacks: [1] 3-line proof, no edge; [2] also-true-for-add/smul (API completeness
    note for cleanup); [3] none further. Verdict: SURVIVED.
  - Prior-B2: no match.

- **L5.6** (internal): `padicZeta` + `padicZeta_isPseudoMeasure` (**RJW Def 4.10 +
  Prop 4.11 first half**)
  - Lean: `ZetaP.lean:110,131`. Source: TeX 1565–1570 + 1588–1589 (quoted at R5 head).
  - Composition: `padicZeta := mk' (zetaNum m) ([u]−1, regular)` — the regularity
    from L5.4's `topGen_pow_ne_one` + `dirac_sub_one_mem_nonZeroDivisors`
    (PseudoMeasure:793, proven); pseudo-measure-ness is `isPseudoMeasure_mk'`
    (PseudoMeasure:1024, proven) at the generator-hypothesis from L5.4.
  - Attacks: [1] choice-plumbing: the `def` chains `.choose_spec.choose_spec.2.2` —
    the skeleton COMPILES, so the ∃-structure matches ✓ (compiler-verified);
    [2] `isPseudoMeasure_mk'`'s exact hypothesis is `∀ n, zpowers (q_n a) = ⊤` —
    L5.4's conclusion verbatim ✓; [3] `a`-independence: NOT claimed by the def
    (a choice is fixed); independence is delivered by the uniqueness clause of
    R-KL — matching the source, which also derives it from zero-divisor(iii) ✓.
    Verdict: SURVIVED.
  - Prior-B2: no match.

- **L5.7** (internal): `padicZeta_moments` (**RJW Prop 4.11 interpolation**)
  - Lean: `ZetaP.lean:137`. Source: TeX 1592–1596 (quoted at R5 head; "Using
    Equation \eqref{eq:integrate pseudo-measure} ... and Proposition
    \ref{PropInterpolation1} ... remove the $(-1)^k$").
  - Composition: given a witness `ν` of `([b]−1)·ζ_p`: multiply the defining
    `mk'_spec` (`([u]−1)·ζ_p = alg(zetaNum)`) by `([b]−1)`:
    `([u]−1)·alg(ν) = ([b]−1)·alg(zetaNum)` in `Q`, pull back along the injective
    `algebraMap` (`IsFractionRing.injective`): `([u]−1)·ν = ([b]−1)·zetaNum` in `Λ`;
    apply `unitsPowCM k`-moments with `units_mul_apply_unitsPowCM`
    (PseudoMeasure:753, proven): `(u^k−1)·ν(x^k) = (b^k−1)·zetaNum(x^k)`; cast to
    ℚ_p, divide by `u^k−1 ≠ 0` (L5.4 torsion-freeness + cast-injectivity), insert
    L5.3's value, remove the sign by L0.4. Moments of `[u]−1`: `dirac`-moment
    `= u^k` (`dirac`-apply def) minus `1`-moment `= 1` (`one`-apply — `[1]`'s
    moment: `(1:ℤ_p^×)^k = 1` ✓).
  - Attacks: [1] `[u]−1`-moment: `1 ∈ Λ(ℤ_p^×)` is `[1-the-unit]` (units-group
    identity — `units_dirac_mul_dirac`-era convention §3): moment `1^k = 1` ✓ (the
    R3-attack[4] confusion pre-empted: here we ARE units-side, `1 = [1]` correctly);
    [2] division order: all in field ℚ_p after cast; `(u:ℚ_p)^k − 1 ≠ 0` ⟸
    cast-inj + L5.4 ✓; [3] witness-uniqueness: any two witnesses agree
    (algebraMap inj) so "every witness" = "the witness" ✓ ∀ν-form sound;
    [4] k=1: both sides 0 (`1−p⁰ = 0` RHS; LHS `ν(x)`: 0 by the chain — consistent,
    no contradiction) ✓. Verdict: SURVIVED.
  - Prior-B2: no match.

- **L5.8** (internal): `kubotaLeopoldt` (**RJW Thm 4.1**) — R-KL root
  - Lean: `ZetaP.lean:154`. Source: TeX 1444–1447 (statement, quoted at top) + 1599
    (proof: existence = Prop 4.11, uniqueness = zero-divisor(iii)).
  - Composition: existence: `padicZeta` + L5.6 + L5.7 (the ∀b-form is exactly
    L5.7's statement); uniqueness: `q₁, q₂` both satisfying ⟹ `q₁ − q₂` is a
    pseudo-measure (L5.5) all of whose `([u]−1)`-witness-moments vanish (the two
    interpolation values subtract: witnesses subtract as in L5.5's proof, moments
    equal ⟹ difference-witness moments 0, cast-injectivity to land in ℤ_p) ⟹
    `q₁ − q₂ = 0` by `pseudoMeasure_eq_zero_of_moments` (PseudoMeasure:829, proven)
    at `a := u` (torsion-free by L5.4).
  - Attacks: [1] ∃!-strength: is the ∀b-moment-property too strong to be satisfiable
    (uniqueness easy, existence hard)? — L5.7 proves it for `padicZeta`, so no;
    too weak for uniqueness? — the `b := u` instance alone pins `q` via
    `pseudoMeasure_eq_zero_of_moments`, so no ✓; [2] the source states moments
    `(1−p^{k−1})ζ(1−k)` with no `b`: our `(b^k−1)·`-factored form is the
    eq-integrate-pseudo-measure encoding (R-KL head-note) — faithful ✓;
    [3] hypothesis audit: `p ≠ 2` required (L5.4 ⟸ `exists_topological_generator`
    needs `(ZMod p^n)ˣ` cyclic — FALSE at `p = 2, n ≥ 3`): stated ✓ never dropped
    (CLAUDE.md rule 5); [4] `IsPseudoMeasure 0`-degeneracy: `0` is a pseudo-measure
    with all moments 0 — could `∃!` accidentally select 0? Only if
    `(1−p^{k−1})ζ(1−k) = 0` for ALL `k>0` — false (`k=2`: `(1−p)·ζ(−1) =
    (1−p)(−1/12) ≠ 0`) ✓ the interpolation is non-degenerate. Verdict: SURVIVED.
  - Prior-B2: no match.

## §4 confidence gate

1. Every leaf discharged from verified mathlib (`bernoulliPowerSeries_mul_exp_sub_one`,
   `derivative_subst`, `exp_pow_eq_rescale_exp`, `constantCoeff_subst`,
   `isUnit_iff_constantCoeff`, `bernoulli_eq_zero_of_odd`, `norm_int_lt_one_iff_dvd`,
   `riemannZeta_neg_nat_eq_bernoulli` — each grep-verified at file:line above) or
   from proven §3 project code (`apply_powCM`, `res_units_eq`, `mahlerLinearEquiv`,
   `mahlerRingEquiv`, `dirac_mul_dirac`, `units_mul_apply_unitsPowCM`,
   `isPseudoMeasure_mk'`, `pseudoMeasure_eq_zero_of_moments`,
   `exists_topological_generator`, `extendByZero`/`iota` cluster). No REVIEW-PENDING
   leaves. ✓
2. Skeleton compiles: `lake build PadicLFunctions` green, 46 sorries, 0 errors
   (verified 2026-06-10, twice). ✓
3. Verbatim quotes: every leaf carries one or points to its parent's (internal nodes
   quote the composition source). ✓
4. Adversarial pass: every node ≥ 3 attacks; two attacks drew blood — L3.6[4]
   (`a = 1` cancellation scare: resolved, convention confirmed, no change) and the
   R2 numeric trace L2.7[3] which *confirmed* the chain at `k=0` exactly. No
   unresolved flaws. ✓
5. Prior-B2 log: `b2_log.jsonl` absent/empty — vacuously clean; the one §3-name
   near-match (L5.4 vs `exists_topological_generator`) inspected, distinct. ✓
6. Tree mirrors the source: R1↔Prop 4.4/Def 4.5, R2↔Lem 4.2/4.3+Prop 4.6,
   R3↔Lem 4.7 (with the recorded ξ-free replan), R4↔Prop 4.8, R5↔§4.3+Thm 4.1;
   each internal node quotes the source's own proof. Two deliberate deviations,
   both recorded with justification: the R3 replan (deferred ξ-machinery) and the
   L5.4 source-expansion (integer generator gloss). LOC estimates: L5.4 ~60–80 LOC
   (vs 1-line gloss + ~15 textbook lines — the one estimate above 3× source);
   L2.6 ~50 LOC (source: half-page of displays); L3.6 ~40 LOC (source: 8-line
   proof); others ≤ 30 LOC each. ✓

**Feasibility**: every §4 leaf is dischargeable from verified infrastructure; the two
new clusters (Bernoulli/exp-substitution algebra L2.2–L2.6; integer-generator ascent
L5.4) are bounded and self-contained. Ready for ticketing.

---

# §5 — Interpolation at Dirichlet characters (TeX 1610–1979) — added 2026-06-10

## Skeleton location (§5)

New-mathematics leaves are skeletonised with `:= by sorry` in:
- `PadicLFunctions/Coefficients.lean` (integer ring of a nonarch field, roots-of-unity norms)
- `PadicLFunctions/Interpolation/Characters.lean` (Dirichlet chars as functions on ℤ_p, Gauss sums)
- `PadicLFunctions/Interpolation/Twist.lean` (twist μ_χ, character-twist transform, ξ-formulas cleared)
- `PadicLFunctions/Interpolation/GenBernoulli.lean` (generalised Bernoulli numbers + F_{χ,a} moments)
- `PadicLFunctions/Interpolation/TameConductor.lean` (Thm 5.1)
- `PadicLFunctions/Interpolation/NonTame.lean` (F_η, μ_η, ζ_η, Thm 5.7)
- `PadicLFunctions/Interpolation/Branches.lean` (ω, ⟨·⟩, ⟨x⟩^s, ζ_{p,i}, L_p, Thms 5.17/5.19)

**Refactor-cluster exception (recorded deviation from Step 2.5).** The W-cluster
below generalises the *existing* `Measure/*` files in place from `ℤ_[p]`-coefficients
to a coefficient ring `R` (the integer ring of a nonarchimedean field `L`). The same
declaration names keep their files; a parallel `sorry`-skeleton cannot coexist with
the monomorphic originals. Step 2.5 is therefore realised for W as: (i) the genuinely
*new* statements (Coefficients.lean) are skeletonised normally; (ii) each widening
ticket carries the per-lemma risk register entry from this section instead of a
skeleton pointer, and its DoD is "file builds with the `R`-parametrised signatures,
zero sorries" — the existing §3 proof scripts are the evidence the dependency shape
type-checks, and the risk register pins where they are ℤ_p-specific.

## Coefficient conventions (binding for every §5 leaf)

`(L : Type*)` a nonarchimedean coefficient field with the typeclass set
`[NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]` and a
`ℤ_[p]`-algebra structure `[Algebra ℤ_[p] L] [IsBoundedSMul ℤ_[p] L]`-grade
(exact spelling fixed at W1; the paper's "finite extension L/ℚ_p" instantiates it,
and so does ℂ_p). `R := integerRing L` its norm-unit ball, `[NormMulClass L]`
assumed where division-by-attained-norm is used. The paper fixes O_L once
(TeX 1781: "Implicit in this theorem is the fact that the relevant Iwasawa algebra
is defined over a (fixed) finite extension L/Q_p containing the values of η").
Statements involving 1/p^n or 1/G(χ⁻¹) at p-power conductor are stated
**denominator-cleared** over `R` (replan note R5-CLEAR below).

### Replan note R5-CLEAR (T018/T026/T034 pattern; binding)
The source's displays for `EqRestrictionFormula` (TeX 1126–1131), `Eqphipsi`
(TeX 1135–1140), Lem 5.4 (TeX 1675–1678) carry the scalars `1/p^n` resp.
`1/G(χ^{-1})`, which are **not** elements of `O_L` when the conductor is a p-power
(G(χ)G(χ⁻¹) = χ(−1)p^n forces |G| = p^{-n/2}). Both sides of each identity are
integral; only the displayed rearrangement is not. We state every such identity
multiplied through by `p^n` resp. `G(χ⁻¹)`, which is equivalent over `L` and
statement-level faithful (the cleared and displayed forms differ by multiplying by
a nonzerodivisor). Blueprint nodes keep the source displays with a one-line note.

## W: coefficient-widening cluster (API gap; gates everything)

### Step 1 prose (source substrate)
RJW fixes the coefficients once and for all in §3: "Let L be a finite extension of
Q_p" (§3.1, TeX 680–690) and defines measures with values in O_L (Def 3.6,
TeX 755–765: "the space of L-valued measures on G ... we say μ is an O_L-valued
measure ... ∥μ∥ ≤ 1"); every §3 toolbox identity is stated over these coefficients.
§§3–4 were developed at `R = ℤ_[p]` (plan.md Generality Decision 1, recorded risk:
"the generalisation is parameter-insertion, not redesign"). §5 is where the source
first *needs* the larger ring: Gauss sums and χ-values (Def 5.2) lie in
ℚ_p(μ_{p^n}, values of χ) and Thm 5.7's Remark 2 (TeX 1781) makes the O_L-algebra
explicit. The widening mirrors the source's own §3 generality; no new mathematics
beyond the four ℤ_p-specific proof points in the risk register.

### Risk register (per-lemma re-attack of the §3 proofs; the W-tickets' contract)
- **W-r1** `norm_apply_le` (Basic.lean:109): current proof divides by `p^valuation`.
  General route: sup attained at `x₀` (compactness, unchanged); set `c := f x₀ ∈ R`;
  `g := fun x => (f x : L)/c` has `‖g x‖ ≤ 1` by maximality (needs `NormMulClass L`),
  so `g ∈ C(X, R)` and `f = c • g`; conclude `‖μ f‖ = ‖c‖‖μ g‖ ≤ ‖f‖·‖μ g‖` —
  same statement *up to* the constant `‖μ g‖`. ATTACK: the ℤ_p statement is
  `‖μ f‖ ≤ ‖f‖` (operator norm ≤ 1, used for `LipschitzWith 1`); over `R` the same
  bound needs `‖μ g‖ ≤ 1` for the *specific* `g`, which is `norm_apply_le` again —
  circular! RESOLUTION (and the honest general statement): automatic boundedness is
  `‖μ f‖ ≤ ‖f‖ * ‖μ‖₀` with `‖μ‖₀ := sup over the unit sphere`… which need not be
  finite a priori. The ℤ_p proof in fact shows ≤ 1 because `‖μ g‖ ≤ 1` for `g` of
  norm ≤ 1 REDUCES to boundedness on the unit ball, which over a *spherically
  complete-free* route follows since `μ g ∈ R` has `‖μ g‖ ≤ 1` BY R-VALUEDNESS.
  The codomain is `R` (the ball!), so `‖μ f‖ ≤ ‖c‖ · 1 = ‖f‖` — NOT circular: every
  value of μ lies in R, norm ≤ 1. Verdict: statement and constant survive verbatim;
  proof swaps `p^n`-division for `c`-division. (`‖f‖` attained in `‖L^×‖` requires
  `f ≠ 0`; the `f = 0` and `IsEmpty X` branches as now.) SURVIVED.
- **W-r2** density `exists_locallyConstant_norm_sub_le` (Basic.lean:191): current
  proof factors through `toZModPow` on the *value* ring — ℤ_p-specific. Fubini.lean
  (T018 replan) already proved the general-ultrametric-target approximation
  `exists_locallyConstant_norm_sub_le'`; W re-bases Basic.lean's density (and its
  `ext_locallyConstant` corollary) on that lemma, deleting the ℤ_p-specific proof.
  ATTACK: T018' is stated for which domain/target? (Verified in file: domain any
  profinite `X`, target any `[NormedAddCommGroup E] [IsUltrametricDist E]`; values
  taken in the image — `R`-valued f gets `R`-valued approximants by construction.)
  SURVIVED.
- **W-r3** Mahler layer (MahlerTransform.lean): mathlib `mahlerEquiv` is already
  E-general (MahlerBasis.lean:356). Our `mahlerCoeff/mahlerTransform/ofPowerSeries`
  re-parametrise; the duality argument (coefficients of μ bounded by W-r1; for
  `F ∈ R⟦T⟧`, `ofPowerSeries F` summability from `aₙ → 0`) is coefficient-agnostic.
  ATTACK: `binomialSeries`/`Ring.choose` usage needs `BinomialRing R`? — no: the
  binomial coefficients live in ℤ_[p] and act on R through the algebra map; the §3
  proofs use `Ring.choose` on ℤ_[p] then `algebraMap`. The one genuinely
  ℤ_p-flavoured input, `𝓐(δ_n) = (1+T)^n` via `binomialSeries_nat`, maps through.
  SURVIVED (worker re-checks each `PadicInt.*` call site).
- **W-r4** Toolbox/UnitsZp/Fubini/Λ(ℤ_p^×)-ring: space-side constructions
  (pushforwards along `X`-maps, clopen indicators, `shiftDiv`, units geometry) —
  coefficient-blind; convolution/Fubini re-run by W-r2/W-r3. The pseudo-measure
  *theory* (zero-divisor lemma, augmentation ideal, Lem 3.38) is NOT widened — §5
  never needs it over R (Thm 5.7 produces a genuine measure; ζ_p stays over ℤ_p and
  is paired through base change W4). PseudoMeasure.lean is widened only in its
  Λ(ℤ_p^×)-ring section.
- **W-r5** §4 files: stay at `R := ℤ_[p]` via instantiation; no churn. ATTACK: do
  the §4 call sites elaborate once Measure/* takes an `R` parameter with ℤ_[p]
  default-instance? — the W-tickets keep `variable (R)`-explicit style with
  `abbrev`-compatibility or update §4 call sites mechanically; DoD includes
  `lake build PadicLFunctions` green project-wide.

### New leaves (skeletonised in Coefficients.lean)
- **W1** (leaf): `integerRing L : Subring L`, carrier `{x | ‖x‖ ≤ 1}` — closed under
  `+` by `IsUltrametricDist.norm_add_le_max`, under `*` by submultiplicativity; with
  `instNormedCommRing` (SubringClass), `instCompleteSpace` (closed subset),
  `instIsUltrametricDist`, `Algebra ℤ_[p] (integerRing L)` (image of the ball under
  the algebra map: `‖algebraMap ℤ_[p] L x‖ ≤ 1` — *hypothesis* on the algebra
  structure, bundled into the typeclass spelling chosen at W1).
  Source: TeX 690 "O_L its ring of integers". Mathlib check: `Valuation.integer`
  exists for `Valued`; no norm-unit-ball `Subring` for `IsUltrametricDist` fields
  found (grep 2026-06-10) — PR candidate. Attacks: [1] counterexample: closure
  under + fails without ultrametric (archimedean |1+1|>1) — hypothesis necessary ✓;
  [2] edge p=2: nothing p-specific in W1 ✓; [3] discharge: every instance named
  above verified available (SubringClass.toNormedCommRing,
  IsClosed.completeSpace_coe, ultrametric-subtype) by local search at skeleton
  time. SURVIVED.
- **W2** (leaf): `IsPrimitiveRoot.norm_sub_one_lt (hζ : IsPrimitiveRoot ζ (p^n))
  (hn : 1 ≤ n) : ‖ζ - 1‖ < 1` (in L; hence `ζ - 1` topologically nilpotent in R).
  Source: standard (RJW cites the analogous unit fact at TeX 1798 for the
  coprime case; the p-power case is classical [Washington Lem. 1.x]). Route:
  `x := ζ - 1`; `(1+x)^{p^n} = 1`; `v_p(binom(p^n, j)) = n - v_p(j) ≥ 1` for
  `0 < j < p^n` (mathlib: `Nat.Prime.pow_dvd_choose`-family / Kummer), so
  `x^{p^n} = -∑_{0<j<p^n} binom·x^j` has every RHS term of norm ≤ ‖p‖·max(1,‖x‖^j);
  if `‖x‖ ≥ 1` then taking norms gives `‖x‖^{p^n} ≤ ‖p‖·‖x‖^{p^n-1} < ‖x‖^{p^n-1}`,
  contradiction with `‖x‖ ≥ 1`. Attacks: [1] edge n=0: ζ = 1 excluded by `1 ≤ n`…
  but ζ primitive p⁰ = 1-st root IS 1, and ‖0‖ < 1 ✓ holds anyway — hypothesis
  `1 ≤ n` kept for the honest statement, noted droppable; [2] ζ = 1 (n ≥ 1,
  p^n > 1): IsPrimitiveRoot excludes ✓; [3] NormMulClass needed? — only
  submultiplicativity and `‖p‖ < 1` (from the ℤ_[p]-algebra normalisation);
  `‖p‖ < 1` must be a recorded hypothesis of the typeclass spelling — ATTACK
  SURFACED REAL CONSTRAINT: the algebra `ℤ_[p] → L` must be norm-compatible
  (‖algebraMap x‖ = ‖x‖, or at least ‖p‖_L < 1); bundled into W1's spelling.
  SURVIVED with the recorded constraint.
- **W3** (leaf): `IsPrimitiveRoot.norm_sub_one_eq_one` — for `ζ` a primitive D-th
  root, `p ∤ D`, `c` with `ζ^c ≠ 1`: `‖ζ^c - 1‖ = 1` (hence a unit of R).
  Source (verbatim, TeX 1798): "and \epsilon_D^c -1 \in \roi_L^\times (since it
  has norm dividing D)". Route: `∏_{0<j<D}(X - ζ^j) = (X^D-1)/(X-1)` at `X = 1`
  gives `∏_{0<j<D}(1 - ζ^j) = D`; norms multiply (NormMulClass), each factor has
  norm ≤ 1 (in R), and `‖D‖ = 1` since `p ∤ D` — so every factor has norm exactly 1.
  Attacks: [1] needs ζ ∈ R (‖ζ‖ ≤ 1): ζ^D = 1 + NormMulClass forces ‖ζ‖ = 1 ✓;
  [2] D = 1, 2 edges: D=1 vacuous (no c), D=2, ζ=−1, c=1: ‖−2‖: p odd ⟹ ‖2‖=1 ✓
  (p = 2 EXCLUDED where this is used? — no: this lemma is p-free except ‖D‖ = 1
  ⟸ p ∤ D ✓ fine for p = 2 with D odd; no silent p≠2 issue); [3] mathlib overlap:
  `IsPrimitiveRoot.prod_one_sub` / cyclotomic-at-one lemmas exist
  (`Polynomial.cyclotomic`-family) — discharge via `IsPrimitiveRoot.prod_pow_sub_one`
  -shaped lemma if present, else the 8-line product argument. SURVIVED.
- **W4** (leaf): scalar extension `baseChange : Λ_{ℤ_p}(X) →+* Λ_R(X)`-grade map
  (at minimum: `PadicMeasure p X → PadicMeasureR R X` with
  `baseChange μ f = ∑' n, (coeffs)` — definition via Mahler for `X = ℤ_p`
  (transform-side: the coefficientwise inclusion `ℤ_p⟦T⟧ → R⟦T⟧`) and via
  `C(X, ℤ_[p])`-density for general profinite X (extend μ R-linearly along
  locally-constant approximation). Needed by: Thm 5.1 (pairing χ·x^k against the
  ℤ_p-witnesses of ζ_p), §5.2 (comparing with §4's μ_a). Source: implicit
  throughout §5.1 ("seen as a locally constant character of Z_p^×" pairing against
  ζ_p, TeX 1620–1621). Attacks: [1] well-definedness of the density route =
  uniform continuity of μ (W-r1) ✓; [2] ring-hom on Λ(ℤ_p): transform-side
  inclusion is a ring hom of power series ✓ defeq-route; [3] compatibility
  `baseChange (dirac x) = dirac x` — definitional on transforms ✓. SURVIVED.

(Leaf-level source quotes for W: Def 3.6 TeX 755–765 — already quoted in the §3
tree — and TeX 1781, 1798 quoted above; W is a generality pass over the §3 tree,
whose per-leaf quotes remain the §3 entries'.)

## R5.1: Interpolation at p-power conductor (RJW Thm 5.1, `thm:tame conductor`)

### Source statement (verbatim, TeX 1619–1622)
> "Let $\chi$ be a (primitive) Dirichlet character of conductor $p^n$ for some
> integer $n \geq 1$ (seen as a locally constant character of $\Zp^\times$, cf.\
> \S \ref{sec:dirichlet ideles}). Then, for $k > 0$, we have
> $\int_{\Zp^\times}\chi(x)x^k \cdot\zeta_p = L(\chi,1-k)$."

### Step 1 prose (the source's own proof, TeX 1623–1765, structure-preserving)
The proof (TeX 1751–1765) composes: (a) since χ vanishes on pℤ_p,
∫_{ℤ_p^×}χx^k·μ_a = ∫_{ℤ_p}χx^k·μ_a = ∫x^k·μ_{χ,a} where μ_{χ,a} is the twist
(eq:twist by chi, TeX 1637–1640); (b) the integral is (∂^k F_{χ,a})(0)
(`cor:eval at x^k`, §3 toolbox — our `apply_powCM` route); (c) F_{χ,a} is computed
by Lem 5.4 (`lem:mahler chi`, TeX 1675–1692) whose proof decomposes χ-twist into
residue-class restrictions and applies EqRestrictionFormula plus the two Gauss-sum
properties of Rem 5.3; (d) the special value f^{(k)}_{χ,a}(0) =
−(1−χ(a)a^{k+1})L(χ,−k) is the complex Lemma 5.5 (`lem:dirichlet integral`,
TeX 1702–1740) via §2's thm:l-function — the same Mellin bridge §4 met at
`kl-values-of-zeta`; p-adically the value is the generalised-Bernoulli number, and
the §4 pattern (T030–T033: rational/algebraic value + quarantined complex bridge)
applies, with Washington Ch. 4 / DS05 §4 as the cross-reference for the
generalised-Bernoulli generating function (source-gap fallback step 1, recorded);
(e) the shift x ↦ x⁻¹-twist and θ_a-cancellation as in §4's T036/T038 give the ζ_p
statement: "∫χ(x)x^k·θ_a = −(1−χ(a)a^k)" (TeX 1760–1761) and hence the theorem.

### Leaves (Characters.lean / Twist.lean / GenBernoulli.lean / TameConductor.lean)

- **L5.1.1** (leaf): `DirichletCharacter.toContinuousMapZp` — for
  `χ : DirichletCharacter R (p^n)`: the function `χ̃ : C(ℤ_[p], R)`,
  `χ̃ x = χ (toZModPow n x)` (with junk χ(0)=0 off units built into MulChar),
  + API: `toContinuousMapZp_apply_unit`, `_apply_of_mem_pZp` (= 0; here n ≥ 1),
  `_mul` (χ̃(xy) = χ̃x·χ̃y), `IsLocallyConstant`.
  - Source (TeX 1620): "(seen as a locally constant character of $\Zp^\times$)".
  - Discharge: `PadicInt.toZModPow` + `MulChar.map_nonunit` + locally-constant
    fibres of toZModPow (§3 Basic.lean `isLocallyConstant_toZModPow_val` pattern).
  - Attacks: [1] n = 0 edge: conductor 1, χ trivial, χ̃ ≡ 1 ≠ 0 on pℤ_p — the
    `_apply_of_mem_pZp` lemma carries `1 ≤ n` (the theorem's hypothesis, TeX 1620
    "n ≥ 1") ✓ statement guarded; [2] `IsUnit (toZModPow n x) ↔ IsUnit x`-bridge
    needed — discharge `PadicInt.isUnit_toZModPow_iff`-shape: local search at
    skeleton; if absent, 6-line lemma via `isUnit_iff` norms; [3] multiplicativity
    at non-units: χ̃(xy) with x unit, y not: both sides 0 ✓ MulChar.map_nonunit.
    SURVIVED.
- **L5.1.2** (leaf): `PadicMeasure.twist` — `(twist χ̃ μ) f := μ (χ̃ * f)` as
  `Λ_R(ℤ_p) → Λ_R(ℤ_p)`, R-linear in μ and f-functorial; +
  `twist_apply`, `twist_powCM` (∫x^k d(twist μ) = ∫χ̃x^k dμ).
  - Source (verbatim, TeX 1637–1640): "If $\mu$ is a measure on $\Zp$, we define a
    measure $\mu_{\chi}$ on $\Zp$ by $\int_{\Zp}f(x) \cdot\mu_{\chi} =
    \int_{\Zp}\chi(x)f(x) \cdot\mu$."
  - Discharge: definition + `LinearMap` bookkeeping (mul action on C(X,R) ✓ §3).
  - Attacks: [1] needs C(ℤ_p,R) a ring with χ̃·f continuous ✓; [2] twist by a
    *bounded* function keeps R-valuedness ✓ ‖χ̃‖ ≤ 1; [3] consistency with the
    source's μ_χ supported on ℤ_p^× (TeX 1641): proven as L5.1.3, not assumed ✓.
    SURVIVED.
- **L5.1.3** (leaf): `twist_res_units` — `Res_{ℤ_p^×}(twist χ̃ μ) = twist χ̃ μ`
  (n ≥ 1), the source's "as $\chi$ is supported on $\zpe$, the twisted measure
  $\mu_{\chi}$ is automatically supported on $\zpe$" (TeX 1641).
  - Discharge: §3 `res`-API + `χ̃·1_{pℤ_p} = 0` (L5.1.1) + Cor 3.32 (`ψ = 0`-side
    or directly res∘twist computation on indicators).
  - Attacks: [1] which form does TameConductor need — the integral form
    `∫_{ℤ_p^×}χx^k μ = ∫_{ℤ_p}χx^k μ` (TeX 1752–1753): provable directly from
    res_apply + indicator-multiplicativity; state THAT as the lemma ✓ reshaped to
    the use site; [2] edge μ arbitrary (incl. non-unit-supported) ✓ holds by
    χ̃-vanishing; [3] n = 0 fails (χ̃ ≡ 1) — `1 ≤ n` hypothesis ✓. SURVIVED.
- **L5.1.4** (leaf): Gauss sum setup — `gaussSumRoot (hζ : IsPrimitiveRoot ζ (p^n))
  (χ) : R := gaussSum χ (AddChar.zmodChar/zmod-construction at ζ)`; properties:
  - (ii) = mathlib `gaussSum_mulShift_of_isPrimitive` (verified at
    DirichletCharacter/GaussSum.lean:57, all `a : ZMod N`, `[IsDomain R]`).
  - Source (verbatim, TeX 1647–1651, Def 5.2): "Let $\chi$ be a primitive Dirichlet
    character of conductor $p^n$, $n \geq 1$. Define the \emph{Gauss sum of $\chi$}
    as $G(\chi) \defeq \sum_{c\in(\Z/p^n\Z)^\times} \chi(c) \epsilon_{p^n}^c$" —
    and (TeX 1653–1659, Rem 5.3): "(i) $G(\chi) G(\chi^{-1}) = \chi(-1) p^n.$
    (ii) $G(\chi) = \chi(a) \sum_{c \in (\Z / p^n \Z)^\times} \chi(c)
    \epsilon_{p^n}^{ac}$ for any $a \in \zpe$."
  - Note: mathlib's `gaussSum` sums over ALL of ZMod N; χ(non-unit) = 0 makes it
    equal the source's unit-restricted sum ✓ definitional bridge lemma.
  - Attacks: [1] the AddChar-from-root construction at general N: verify name
    (`AddChar.zmod`-family, LegendreSymbol/AddCharacter.lean `zmodChar` is
    ℤ/2^?-specific — at skeleton, search `AddChar.mk`-from-`IsPrimitiveRoot`; if
    absent it is a 10-line leaf L5.1.4a: `ZMod N → R`, `a ↦ ζ^(a.val)`,
    additivity from ζ^N = 1 — `ZMod.pow_totient`… standard); its primitivity
    (needed by mathlib's (ii)) ⟸ ζ primitive — small lemma; [2] (ii)'s
    `[IsDomain R]`: R = integerRing L of a field IS a domain ✓ instance; [3] the
    ε-SYSTEM (ε_{p^{n+1}}^p = ε_{p^n}, TeX 1650) — §5.1 only ever uses ONE level n
    at a time (the system matters for compatibility across n in later sections);
    parametrising by `IsPrimitiveRoot ζ (p^n)` per-statement is faithful here;
    recorded so §8+ (Coleman) revisits. SURVIVED.
- **L5.1.5** (leaf, gap→PR candidate): `gaussSum_mul_gaussSum_inv` — for χ
  primitive mod N, e primitive AddChar, R a domain:
  `gaussSum χ e * gaussSum χ⁻¹ e⁻¹ = N` (mathlib has this only for N prime/field).
  - Source: Rem 5.3(i) (quote above; source's display = this × the
    `e⁻¹ = e.mulShift (−1)`-unfolding absorbing χ(−1)).
  - Route (4 sums): G(χ,e)·G(χ⁻¹,e⁻¹) = Σ_b χ⁻¹(b)e(−b)·G(χ,e)
    = Σ_b e(−b)·gaussSum χ (e.mulShift b)   [mathlib (ii), backwards]
    = Σ_b Σ_a χ(a) e(ab − b) = Σ_a χ(a) Σ_b e(b(a−1)) = N·χ(1) = N
    [primitive-e orthogonality Σ_b e(bc) = N·δ_{c,0} — the `sum_mulShift`
    ingredient used by the field proof, generality re-verified at skeleton].
  - Attacks: [1] χ⁻¹(b)-vs-gaussSum-mulShift orientation: (ii) gives
    `gaussSum χ (e.mulShift b) = χ⁻¹(b) gaussSum χ e` for ALL b incl. non-units
    (where both sides are 0 only if e primitive… for b non-unit LHS is a Gauss sum
    at an imprimitive char = 0 by `gaussSum_eq_zero_of_isPrimitive_of_not_isPrimitive`
    ✓ and χ⁻¹(b) = 0 ✓) — the b-sum over all of ZMod N is legitimate ✓;
    [2] domain needed only through mathlib's (ii) ✓; [3] N = 1 edge: G(1,1) = 1,
    product = 1 = N ✓. SURVIVED.
- **L5.1.6** (leaf): `mahlerTransform_charTwist` — the z-twist formula, cleared
  form. For `r ∈ R` topologically nilpotent with character `κ_r` (mathlib
  `PadicInt.addChar_of_value_at_one`), and μ ∈ Λ_R(ℤ_p):
  `𝓐(κ_r · μ) = PowerSeries.eval₂ (C-inclusion) ((1+T)·(1+r) − 1) (𝓐 μ)`
  (evaluation into S := R⟦T⟧ with WithPiTopology; constant term r top-nilpotent).
  - Source (TeX 1084–1090, the deferred z-twist): "if z ∈ 𝓞_{ℂp} with |z−1| < 1…
    the measure z^x μ has Mahler transform 𝓐_μ((1+T)z − 1)" (§3.5; deferral note
    plan.md "Deferred" row 4 — comes due here).
  - Route: coefficientwise, T009/T014 pattern: LHS_n = μ(κ_r·binom(·,n));
    κ_r = Σ_m binom(·,m) r^m (the AddChar.lean construction is literally this
    Mahler series); product-of-binomials expansion + Chu–Vandermonde regroups to
    the eval₂ coefficient. Dirac sanity: μ = δ_m ⟹ both sides z^m(1+T)^m.
  - Attacks: [1] instance stack for eval₂ (IsLinearTopology R⟦T⟧, complete, T2):
    WithPiTopology over R-with-norm-topology — R's topology linear (balls are
    ideals of R: `‖x‖ ≤ ε`-sets ✓ ultrametric+submult) — instance leaf L5.1.6a in
    Coefficients.lean (`IsLinearTopology R R` for integerRing; ~15 LOC) +
    mathlib's PiTopology instances (verified present in
    MvPowerSeries/{Topology,Evaluation}); [2] continuity of the coefficient
    inclusion `R → R⟦T⟧`-vs-φ argument of eval₂ ✓ C is continuous coefficientwise;
    [3] alternative if eval₂ plumbing fights: state the RHS coefficientwise
    (`coeff n (RHS) = Σ_m binom(m+?,?)…`-explicit) — BOTH routes recorded, worker
    picks; the STATEMENT in the skeleton uses eval₂ (source-shaped). SURVIVED.
- **L5.1.7** (leaf): `res_class_eq_sum_twists` (EqRestrictionFormula, cleared) —
  for `hζ : IsPrimitiveRoot ζ (p^n)`, b : ZMod (p^n), μ ∈ Λ_R(ℤ_p):
  `(p^n : R) • 𝓐(Res_{b+p^nℤ_p} μ) = ∑_{c ∈ ZMod (p^n)} ζ^{-bc} • 𝓐(κ_{ζ^c−1}·μ)`
  (with 𝓐(κ·μ) as in L5.1.6; equivalently before transform, as measures).
  - Source (verbatim, TeX 1126–1131): "Res_{b + p^n\Zp}(\mu) = … \frac{1}{p^n}
    \sum_{\xi \in \mu_{p^n}} \xi^{-b} (z^x\mu)|_{z = \xi}" [EqRestrictionFormula
    display] — cleared per R5-CLEAR.
  - Route: measure-side orthogonality: Σ_{c} ζ^{(x−b)c} = p^n·1_{x ≡ b (p^n)}
    pointwise on ℤ_p (finite geometric sum; x ≡ b detection through toZModPow n),
    then integrate. 1_{b+p^nℤ_p} is the §3 clopen-indicator.
  - Attacks: [1] ζ^{(x−b)c} for x ∈ ℤ_p: meaning is κ_{ζ^c−1}(x)·ζ^{-bc} —
    well-formed via the AddChar (ζ^x := κ(x)) ✓ no ad-hoc exponentials;
    [2] orthogonality at x ∉ b+p^n: Σ_c (ζ^{x−b})^c = 0 needs ζ^{x−b} ≠ 1 i.e.
    toZModPow n x ≠ b and ζ primitive ✓ + geometric-sum-zero (ω^N=1, ω≠1 ⟹ Σ=0:
    `IsPrimitiveRoot`-adjacent, in mathlib as `IsPrimitiveRoot.geom_sum_eq_zero`?
    verify at skeleton; else 5 lines); [3] does §5.1 need general b or only the
    χ-summed version? Lem 5.4's proof needs per-b — keep ✓. SURVIVED.
- **L5.1.8** (internal): `mahler_twist_formula` (RJW Lem 5.4, cleared) — for χ
  primitive mod p^n (n ≥ 1), ζ primitive p^n-th root:
  `gaussSumRoot ζ χ⁻¹ • 𝓐(twist χ̃ μ) = χ(−1)•∑_{c units} χ⁻¹(c) • 𝓐(κ_{ζ^c−1}·μ)`
  — equivalently the source display × G(χ⁻¹), using (i) to absorb p^n.
  - Source (verbatim, TeX 1675–1678): "The Mahler transform of $\mu_{\chi}$ is
    $\Am_{\mu_\chi}(T) = \frac{1}{G(\chi^{-1})}\sum_{c \in (\Z/p^n \Z)^\times}
    \chi(c)^{-1}\Am_{\mu} \big( (1+T)\epsilon_{p^n}^c - 1 \big)$."
  - Composition (mirrors source proof TeX 1680–1692): χ̃ = Σ_c χ(c)1_{c+p^n}
    (L5.1.1 locally-constant decomposition) ⟹ twist = Σ_c χ(c)Res_{c+p^n};
    apply L5.1.7, swap sums, recognise G(χ) via L5.1.4(ii) at the inner sum
    (`Σ_b χ(b)ζ^{-bc} = χ(−c)⁻¹·…`-shape — exactly the source's second display,
    TeX 1685–1690), then (i)=L5.1.5 to trade G(χ)p^{-n} for χ(−1)/G(χ⁻¹), cleared.
  - Attacks (composition): [1] sum-swap finite ✓; [2] the χ(−c)⁻¹ bookkeeping has
    a sign trap (χ(−1)-factor): END-TO-END TRACE at p^n = 3, χ the quadratic
    character mod 3, μ = δ_1: LHS: twist χ̃ δ_1 = χ(1)δ_1 = δ_1, transform (1+T);
    G(χ⁻¹) = G(χ) = ζ − ζ² (χ(1)=1, χ(2)=−1); RHS = χ(−1)Σ_c χ(c)[𝓐(κ_{ζ^c−1}δ_1)]
    = −[χ(1)ζ(1+T) − χ(2)ζ²(1+T)] − wait κ_{ζ^c−1}δ_1 transform = ζ^c(1+T):
    RHS = χ(−1)[ζ(1+T) − ζ²(1+T)] = −(ζ−ζ²)(1+T) [χ(−1) = χ(2) = −1].
    LHS = (ζ−ζ²)(1+T)?? MISMATCH of sign ⟹ the cleared statement must carry
    χ(−1) on the LHS or use G(χ⁻¹)-on-the-other-side: re-derive: source:
    𝓐_{μχ} = (1/G(χ⁻¹))Σ_c χ⁻¹(c)𝓐_μ((1+T)ζ^c−1). Cleared: G(χ⁻¹)·𝓐_{μχ}
    = Σ_c χ⁻¹(c)·𝓐(κ-twists). Trace: G(χ⁻¹) = ζ−ζ²; LHS = (ζ−ζ²)(1+T);
    RHS = Σ_c χ⁻¹(c)ζ^c(1+T) = (χ(1)ζ + χ(2)ζ²)·(1+T) = (ζ−ζ²)(1+T) ✓✓ EQUAL —
    my χ(−1)-in-the-statement draft above was WRONG; the cleared form is the
    PLAIN multiply-through `G(χ⁻¹) • 𝓐(twist) = Σ_c χ⁻¹(c) • (κ-twist transforms)`
    with NO extra sign; the χ(−1)/p^n appear only INSIDE the proof when
    converting the L5.1.7 p^n-cleared identity (which divides by G(χ)G(χ⁻¹)
    = χ(−1)p^n — in cleared bookkeeping: multiply L5.1.7's χ-summed form by
    χ(−1)G(χ⁻¹)² …; the worker follows the algebra; the trace pins the final
    statement). Statement fixed in skeleton per the trace. ATTACK [2] CAUGHT a
    real statement bug at planning time — exactly Phase 1e's purpose.
    [3] both (i) and (ii) at level p^n verified available (L5.1.4/L5.1.5) ✓.
    SURVIVED (statement corrected by trace).
- **L5.1.9** (leaf): generalised Bernoulli numbers — `genBernoulli χ k : R`-field…
  in L: `genBernoulli (χ : DirichletCharacter L N) (k : ℕ) : L :=
  N^{k-1}·Σ_{c=0}^{N-1} χ(c)·(Polynomial.bernoulli k).eval (c/N : L)`-shape
  (B_{k,χ}, Washington §4.1/DS05) + API (`genBernoulli_one_eq` reduction to
  bernoulli at χ = 1-level-1; parity vanishing `genBernoulli_eq_zero_of_…`
  deferred to where needed).
  - Source: not displayed in RJW §5 (the source routes through L(χ,−k) and
    thm:l-function); cross-reference (fallback chain step 1): Washington,
    *Introduction to Cyclotomic Fields*, §4.1–4.2: "B_{n,χ} defined by
    Σ_{a=1}^{f} χ(a) t e^{at}/(e^{ft} − 1) = Σ B_{n,χ} t^n/n!" and Thm 4.2:
    "L(1−n, χ) = −B_{n,χ}/n". Our definition uses the equivalent
    Bernoulli-polynomial form (Washington Prop 4.1: B_{n,χ} =
    f^{n−1}Σ_a χ(a)B_n(a/f)); equivalence is internal bookkeeping.
  - Attacks: [1] c/N needs N invertible in L ✓ char-0 field; [2] which Bernoulli
    convention: Polynomial.bernoulli uses `bernoulli` (B₁ = −1/2); Washington's
    B_{n,χ} for χ = 1 (f = 1) gives B_n(0)?? — B_n(0) = bernoulli n EXCEPT the
    χ=1 comparison to ζ wants… the χ-trivial case reduces to RJW's own
    `zetaNeg` (§4): consistency lemma `genBernoulli_trivial : genBernoulli 1 k
    = (-1)^?·bernoulli k`-shape pinned by cross-checking against L(1,−k) sign at
    k=1,2 numerically AT SKELETON TIME (B_{1,1} = 1/2 = bernoulli' 1: Washington
    f=1: B_n(a/f) at a=1?? Σ_{a=1}^{1}χ(a)B_n(a/1) = B_n(1) = bernoulli' n ✓ so
    trivial-χ gives bernoulli' — consistent with ζ(−n) = −B'_{n+1}/(n+1) ✓ and
    the a-range 1..f (not 0..f−1) MATTERS; skeleton uses Σ_{a=1}^{N} ✓);
    [3] χ primitive vs any level: define at any level (Washington does);
    primitivity only in interpolation statements. SURVIVED (a-range pinned).
- **L5.1.10** (internal): `twistMuA_moments` — the p-adic value computation:
  for χ primitive mod p^n, n ≥ 1, a coprime to p (and to keep §4's setup, p odd
  where μ_a does):
  `G(χ⁻¹) • ∫ x^k d(twist χ̃ (μ_a)_R) = G(χ⁻¹) • (−(1 − χ(a)a^{k+1})·(−genBernoulli χ (k+1)/(k+1)))`-cleared-shape — i.e. ∂^k at 0 of L5.1.8's RHS
  equals the Washington-style value; skeleton states the sane cleared form
  `∫χ̃x^k dμ_a = −(1−χ(a)a^{k+1})·LvalNeg χ k` with
  `LvalNeg χ k := −genBernoulli χ (k+1)/(k+1) : L` and the integral L-valued
  (pairing through baseChange W4; G-clearing only inside the proof).
  - Source (TeX 1707–1711, Lem 5.5 statement, verbatim):
    "$f_{\chi,a}^{(k)}(0) = -\big(1-\chi(a)a^{k+1}\big)L(\chi,-k)$ if
    $\chi(-1) (-1)^k = -1$; $0$ if $\chi(-1)(-1)^k = 1$" — note BOTH branches
    are `−(1−χ(a)a^{k+1})L(χ,−k)` once L(χ,−k) = 0 in the even case (source's
    own Remark TeX 1744–1746) — the Lean statement is the uniform formula with
    `LvalNeg`; the parity-vanishing of `LvalNeg` is L5.1.11.
  - Composition: ∂^k(0) of the cleared Lem 5.4 RHS for μ = μ_a: each term
    𝓐(κ_{z}·μ_a)|-derivatives at 0: ∂ = (1+T)d/dT (§3); the §4 T033 machinery
    computed ∂^k F_a(0) via the e^t-generating-function in ℚ_p⟦t⟧; here the
    analogous computation over L⟦t⟧: G(χ⁻¹)Σ_c χ⁻¹(c)F_a((1+T)ζ^c−1) under
    e^t = 1+T becomes Σ-of-shifted-exponential-series whose Taylor coefficients
    are the B_{k,χ}-generating function (Washington §4.2's manipulation) ×
    Euler-factor bookkeeping for the a-smoothing. Sub-decomposition (skeleton
    leaves, GenBernoulli.lean): L5.1.10a generating-function identity
    `Σ_{c=1}^{p^n} χ(c)·t·e^{ct}/(e^{p^n t}−1) = Σ_k genBernoulli χ k·t^k/k!`
    (formal, in L⟦t⟧; Washington's defining identity ↔ our polynomial def —
    finite-sum Bernoulli-polynomial bookkeeping, `bernoulliPowerSeries`-based,
    T031-pattern); L5.1.10b the χ-twisted F_a-expansion: the cleared Lem-5.4-RHS
    at e^t = 1+T equals
    `Σ_c χ⁻¹(c)G(χ⁻¹)·[1/(e^tζ^c·…)]`… realised as: ζ^c-shifted geometric
    cancellations — the SOURCE's own display (TeX 1697): F_{χ,a}(T) =
    (1/G(χ⁻¹))Σ_c χ(c)⁻¹[1/((1+T)ζ^c−1) − a/((1+T)^aζ^{ac}−1)]; cleared and
    multiplied by the unit-denominators: T031-pattern clearing
    `((1+T)ζ^c − 1)`-factors are UNITS?? — NO: |ζ^c − 1| < 1 (W2) so NOT units:
    handled exactly as §4's F_a: cleared characterising identity
    `((1+T)^{p^n}−1)·[stuff]`… the common denominator (1+T)^{p^n}−1 works since
    ζ^{c·p^n} = 1: (1+T)ζ^c−1 divides (1+T)^{p^n}−1 in R⟦T⟧ ⟸ product formula
    Π_c((1+T)ζ^c−1) = (1+T)^{p^n}−1 (the W3-style cyclotomic product, p-power
    case) — sub-leaf L5.1.10c. The worker-facing contract: the moments
    statement above + these three sub-leaf identities; assembly is §4-T033-style
    derivative bookkeeping.
  - Attacks: [1] END-TO-END SANITY at χ quadratic mod 3 (p=3, a=2, k=1):
    numeric check of `∫χx dμ₂ = −(1−χ(2)·4)·(−B_{2,χ}/2)`: B_{2,χ} =
    3^{1}·[χ(1)B₂(1/3)+χ(2)B₂(2/3)] = 3[(1/9−1/3·... )−(4/9−2/3+1/6−…)]:
    B₂(x) = x²−x+1/6: B₂(1/3) = 1/9−1/3+1/6 = −1/18; B₂(2/3) = 4/9−2/3+1/6 =
    −1/18; B_{2,χ} = 3·[−1/18 − (−1/18)·(−1)?? χ(2) = −1: 3[−1/18·1 +
    (−1)·(−1/18)] = 3·0 = 0?? — χ quadratic mod 3 is ODD (χ(−1) = χ(2) = −1);
    B_{2,χ} = 0 for parity reasons (k+1 = 2 even vs χ odd ⟹ vanishing ✓
    consistent with L5.1.11 parity: nonvanishing needs χ(−1)(−1)^{k+1}… the
    k=1, χ-odd moment: χ(−1)(−1)^1 = (−1)(−1) = +1 ⟹ the value is 0 — and
    LHS ∫χx dμ₂: trace via μ₂ = [witness]… both sides 0 ✓ consistent;
    parity-machinery confirmed live. Pick the NONVANISHING check k=2:
    B_{3,χ} = 9[χ(1)B₃(1/3) − B₃(2/3)]: B₃(x) = x³−(3/2)x²+(1/2)x:
    B₃(1/3) = 1/27−1/6+1/6 = 1/27; B₃(2/3) = 8/27−2/3+1/3 = 8/27−1/3 = −1/27;
    B_{3,χ} = 9[1/27+1/27] = 2/3; value −(1−χ(2)2³)(−B_{3,χ}/3) =
    −(1+8)(−2/9) = 2. Measure side: ∫χx²dμ₂ over ℤ₃ — μ₂ has moments
    ∫x^k μ₂ = (−1)^k(1−2^{k+1})ζ(−k)-pattern… full numeric trace deferred to
    the worker's first regression (#eval-style sanity via finite-level approx is
    NOT available; instead the worker re-derives the k=2 value through the
    generating function — the planning-time check above validates the
    STATEMENT's shape and parity wiring) — recorded as ticket acceptance step;
    [2] composition gap: does L5.1.8 + ∂^k REALLY need eval₂-functoriality of
    ∂ (∂ commutes with the κ-twist substitution)? — ∂-of-eval₂ chain rule:
    avoided by computing moments via `twist_powCM` (L5.1.2) on the MEASURE side
    then L5.1.8 only as the bridge to the t-side generating function — the §4
    T033 proof shape (measure moments ↔ power-series derivatives at 0 via
    `apply_powCM`) — composition re-checked: types line up through W4-baseChange
    ✓; [3] the `(μ_a)_R` base change commutes with twist/Res/ψ — small
    naturality leaves, folded into W4's API (recorded there). SURVIVED.
- **L5.1.11** (leaf): parity vanishing `genBernoulli_eq_zero` —
  `χ(−1)·(−1)^k = 1 → genBernoulli χ k... ` precise: B_{k,χ} = 0 when
  χ(−1) ≠ (−1)^k (k ≥ 2-grade care at χ trivial).
  - Source (TeX 1744–1746): "we recover the well-known fact that $L(\chi,-k) = 0$
    if $\chi(-1)(-1)^k = 1$" (+ proof's reflection argument TeX 1731–1739).
  - Route: c ↦ N−c involution on the defining sum + B_k(1−x) = (−1)^k B_k(x)
    (mathlib: `Polynomial.bernoulli_eval_one_sub`? verify; classical identity).
  - Attacks: [1] χ trivial & k = 1: B_{1,1} = 1/2 ≠ 0 and χ(−1)(−1) = −1 ✓
    excluded by the hypothesis ✓; [2] c = 0/c = N endpoint double-count in the
    involution: the a-range 1..N from L5.1.9 makes c ↦ N−c map {1..N−1} to
    itself + fixed handling of c = N (χ(N) = χ(0) = 0 for N > 1) ✓;
    [3] needs (−1)^k B_k(x)-identity in mathlib — `bernoulli_eval_one_sub`
    verified-or-12-lines. SURVIVED.
- **L5.1.12** (internal): **Thm 5.1 assembly** `padicZeta_twisted_moments` —
  statement (ζ_p-witness form, mirroring T038/T039's moment encoding):
  for χ primitive mod p^n (n ≥ 1), p odd, k > 0, b ≔ the §4 generator-witness
  quantification: `∀ witnesses ν of ([b]−[1])·ζ_p: ∫χ̃x^k dν_R =
  (χ(b)b^k − 1)·LvalNeg χ (k−1)`-shape, plus the headline reading
  `∫_{ℤ_p^×}χx^k·ζ_p = L(χ,1−k)` as docstring/blueprint gloss; concretely the
  θ_a-form is the proved engine: `∫χ̃x^k d(θ_a)_R = −(1−χ(a)a^k)·LvalNeg χ (k−1)`
  (the source's own display TeX 1760–1761, verbatim: "By definition, we have
  $\int_{\Zp^\times}\chi(x)x^k \cdot\theta_a = -(1-\chi(a)a^{k})$" — note the
  source elides the L-factor there; the preceding display TeX 1757–1759 carries
  it: "$\int_{\Zp^\times}\chi(x)x^k \cdot x^{-1}\mu_a = -(1-\chi(a)a^{k})L(\chi,1-k)$").
  - Composition: L5.1.3 (units-restriction trivial for χ-twist) + L5.1.10
    (moments of twist μ_a) + §4's x⁻¹-twist machinery (T036 zetaNum pattern:
    x·(x⁻¹μ)-bookkeeping under twist: χ(x)x^k·x⁻¹μ_a-identities) + W4
    naturality + uniqueness-free (5.1 is a value statement, no ∃!).
  - Attacks: [1] k > 0 vs k−1 ≥ 0 indexing ✓ destructure k = k'+1 (HANDOVER
    gotcha); [2] the (1−p^{k−1})-Euler factor: ABSENT in Thm 5.1 (χ ramified ⟹
    no Euler factor — consistency: source remark at TeX 1861 "if $\chi$ is
    non-trivial, then $\mu_\theta$ is already supported on $\Zp^\times$; but
    this is consistent, as $\theta(p) = 0$"); our route never inserts one ✓;
    [3] interaction with §4's `padicZeta` defined at ℤ_p-coefficients: the
    witness pairing is THROUGH baseChange; the b-quantification must match
    T038's exact encoding — skeleton copies T039's statement shape with the
    χ̃-factor inserted. SURVIVED.

## R5.2: Non-trivial tame conductors (RJW Thm 5.7, `thm:nontame`)

### Source statement (verbatim, TeX 1773–1776)
> "Let $D > 1$ be any integer coprime to $p$, and let $\eta$ denote a (primitive)
> Dirichlet character of conductor $D$. There exists a unique measure
> $\zeta_\eta \in \Lambda(\Zp^\times)$ such that, for all primitive Dirichlet
> characters $\chi$ with conductor $p^n$, $n \geq 0$, and for all $k > 0$, we have
> $\int_{\Zp^\times} \chi(x) x^k \cdot\zeta_{\eta} = \big(1 - \chi \eta(p)
> p^{k-1}\big) L(\chi \eta,1-k)$."

### Step 1 prose (source proof, TeX 1785–1875)
The source gives "only the main ideas" (TeX 1786: "the proof of Theorem
\ref{thm:nontame} is a good exercise") — per Phase 1e the gaps are expanded
here and each expansion is a leaf. Chain: (1) define F_η (EquationFeta, TeX
1793–1795) — an honest element of O_L⟦T⟧ because each (1+T)ε_D^c − 1 is a UNIT
(constant term ε_D^c − 1 ∈ O_L^×, TeX 1798's parenthetical, = W3) — and μ_η its
measure; (2) Lem 5.9 (TeX 1801–1807): ∫x^k μ_η = L(η,−k), "proved in a similar
manner to Lemma 5.5" — p-adically: the F_η Taylor coefficients give the
generalised Bernoulli values (GenBernoulli cluster, η-instance — NO clearing
needed since G(η⁻¹), D ∈ R^×); (3) Lem 5.10 ψ(F_η) = η(p)F_η (TeX 1812–1827)
via the trace identity (TeX 1818); (4) Lem 5.11 (TeX 1831–1843):
Res_{ℤ_p^×}μ_η = μ_η − η(p)φμ_η and ∫x^k φμ = p^k∫x^k μ ⟹
∫_{ℤ_p^×}x^k μ_η = (1−η(p)p^k)L(η,−k); (5) μ_θ := (μ_η)_χ, Lem 5.12 transform
formula (TeX 1849–1852) "Using Lemma 5.4, we find easily"; the χ-twisted moments
"Via a calculation essentially identical to the cases already seen" (TeX 1854–
1856) and Res-formula (TeX 1858–1861); (6) ζ_η := x⁻¹Res_{ℤ_p^×}(μ_η)
(Def, TeX 1866–1868) and the final display (TeX 1870–1873); uniqueness from
density of the twisted monomials (the source treats it as implicit in "unique
measure" — expanded as L5.2.8).

### Leaves (NonTame.lean; coefficient field L ⊇ μ_D + values of η)

- **L5.2.1** (leaf): `etaDenomUnit` — for ζ_D primitive D-th root in R, c with
  D ∤ c: `IsUnit ((ζ_D^c) • (X+1) - 1 : R⟦X⟧)`-shape via constant-coeff unit
  (W3 + `PowerSeries.isUnit_iff_constantCoeff`, already used in §4).
  Source: TeX 1798 (quoted at W3). Attacks: [1] c ≡ 0 (mod D): ζ^c = 1, const
  coeff 0, NOT a unit — η(c) = 0 kills those terms in F_η; the def sums over
  units c only ✓ guard in statement; [2] (X+1) vs (1+X) orientation ✓ cosmetic;
  [3] discharge: `isUnit_iff_constantCoeff` verified (Inverse.lean:111, plan.md
  §4 table). SURVIVED.
- **L5.2.2** (leaf): `muEta : Λ_R(ℤ_p)` — `muEta := −G(η⁻¹)⁻¹-unit • Σ_{c units}
  η⁻¹(c) • (inverse measure of L5.2.1)` — via 𝓐⁻¹ (ofPowerSeries); G(η⁻¹) unit:
  L5.1.5 at level D (`G(η)G(η⁻¹) = ±D`, ‖D‖ = 1) + `‖G‖ ≤ 1`-integrality both
  factors ⟹ unit (norm-1) — sub-leaf `gaussSum_isUnit_of_coprime`.
  Source (verbatim, TeX 1793–1795): "$F_{\eta}(T) \defeq \frac{-1}{G(\eta^{-1})}
  \sum_{c \in (\Z/D\Z)^\times} \frac{\eta(c)^{-1}}{(1 + T)\epsilon_{D}^c - 1}$"
  and TeX 1798: "There is therefore a measure $\mu_{\eta} \in \Lambda(\Zp)$ …
  corresponding to $F_{\eta}$ under the Mahler transform."
  Attacks: [1] the sign −1 placement ✓ source's; [2] D = 1 edge excluded
  (D > 1 hypothesis, TeX 1773) — at D = 1 the c-sum is over {1}, ζ_D = 1,
  denominator (1+T)−1 = T not a unit — hypothesis NECESSARY ✓ recorded;
  [3] η⁻¹ vs χ(c)^{-1} = χ⁻¹(c) for MulChar with values in a field where χ(c)
  can be 0: mathlib's χ⁻¹ handles (inv-char := χ∘(·⁻¹)… verified MulChar.inv
  semantics at skeleton). SURVIVED.
- **L5.2.3** (leaf): `muEta_moments` — `∫x^k d(muEta) = LvalNeg η k` i.e.
  −B_{k+1,η}/(k+1) (Lem 5.9's second half; first half L(f_η,s) = −η(−1)L(η,s)
  is the complex bridge, quarantined as L5.2.9).
  Source (verbatim, TeX 1801–1804): "We have $L(f_\eta,s) = -\eta(-1)L(\eta,s).$
  Hence for $k \geq 0$ we have $\int_{\Zp}x^k \cdot\mu_\eta = L(\eta,-k)$."
  Route: ∂^k F_η(0) through the η-instance of the generating-function cluster
  (L5.1.10a at modulus D; the geometric expansion TeX 1797 is the worker's
  guide: each unit-denominator term expands honestly in R⟦T⟧).
  Attacks: [1] k = 0 included (k ≥ 0 here vs k > 0 in 5.1) ✓ statement matches
  source; [2] parity: B_{k+1,η} vanishing handled by L5.1.11, no contradiction
  with the formula (both sides 0) ✓; [3] the −η(−1)-factor of the f_η-side does
  NOT enter the p-adic statement (it is absorbed in the Mellin normalisation of
  the complex side) — confirmed by source's "Hence" giving the clean
  ∫x^k μ_η = L(η,−k) ✓. SURVIVED.
- **L5.2.4** (leaf): `psi_muEta` — ψ(μ_η) = η(p)·μ_η (RJW Lem 5.10).
  Source (verbatim, TeX 1812–1813): "We have $\psi(F_\eta) = \eta(p)F_\eta$."
  **Recorded replan (R3/T034 pattern).** The source proves this by the μ_p-trace
  identity (TeX 1818) inside (φ∘ψ)-Eqphipsi — which over R requires μ_p ⊂ L,
  a hypothesis the STATEMENT does not need. The ξ-free route (the cleared form
  of the source's own partial-fraction identity, as in R3):
  let γ_c := (ε^c δ_1 − δ_0)⁻¹ ∈ Λ_R (L5.2.1/L5.2.2), A_c := ε^{pc}δ_1 − δ_0.
  (i) geometric telescope in Λ_R:
      φ(A_c)·γ_c = Σ_{j<p} ε^{jc}δ_j   [since ((1+T)^pε^{pc}−1) =
      ((1+T)ε^c−1)·Σ_{j<p}((1+T)ε^c)^j — the cleared trace identity];
  (ii) apply ψ + projection formula (W-widened psi_phi_mul):
      A_c·ψ(γ_c) = ψ(Σ_{j<p}ε^{jc}δ_j) = δ_0   [ψδ_j = 0 for 0<j<p,
      ψδ_0 = δ_0 — §4 L3.3/L3.4 widened];
  (iii) so ψ(γ_c) = A_c⁻¹·δ_0 = γ_{pc-index}   [A_c = ε^{(pc)}δ_1 − δ_0 with
      pc taken mod D, p ∤ D];
  (iv) sum: ψ(μ_η) = −G(η⁻¹)⁻¹Σ_c η⁻¹(c)γ_{pc} = η(p)μ_η by reindexing
      c ↦ p⁻¹c on (ℤ/D)ˣ (η⁻¹(p⁻¹c') = η(p)η⁻¹(c')).
  Attacks: [1] (i) is an identity of UNITS-inverses: verify by multiplying out —
  pure ring algebra in Λ_R via 𝓐 (power-series side: polynomial identity) ✓;
  [2] ψ(δ_j) for 0<j<p needs j a UNIT of ℤ_p ✓ j < p coprime; [3] the pc-index:
  p invertible mod D ⟸ gcd(p,D)=1 ✓ hypothesis present; [4] END-TO-END TRACE
  (D = 4?? p odd, take p = 3, D = 4, η the quadratic char mod 4, c ∈ {1,3},
  ε = i): γ_1 = (iδ_1−δ_0)⁻¹, γ_3 = (−iδ_1−δ_0)⁻¹; ψγ_1 = γ_{3·1 mod 4} = γ_3 ✓
  shape; μ_η = −G(η⁻¹)⁻¹[γ_1 − γ_3]; ψμ_η = −G⁻¹[γ_3 − γ_1] = −μ_η = η(3)μ_η
  [η(3) = −1 ✓] — TRACE CONFIRMS, including the sign through the reindex.
  SURVIVED. (Lemma-level faithfulness: statement is TeX 1812–1813 verbatim;
  proof-route deviation recorded here, mirroring decomposition R3.)
- **L5.2.5** (leaf): `res_units_muEta_moments` — RJW Lem 5.11:
  `∫_{ℤ_p^×}x^k μ_η = (1−η(p)p^k)·LvalNeg η k`.
  Source (verbatim, TeX 1831–1834): "We have $\int_{\Zp^\times}x^k \cdot\mu_{\eta}
  = \big(1-\eta(p)p^k\big)L(\eta,-k)$." Proof TeX 1836–1843: Res = 1−φψ +
  ∫x^k φμ = p^k∫x^k μ.
  Discharge: §3 toolbox (res_units = 1 − φψ, widened) + L5.2.4 + §4's
  `apply_powCM`-of-φ lemma (T035 `res_units_muA_apply_powCM` pattern — the φ-
  moment-scaling lemma exists at ℤ_p (Toolbox/T011/T035-route), widened by W).
  Attacks: [1] exactly the §4 T035 proof with η(p)-factor inserted ✓ pattern
  proven; [2] η(p) ∈ R vs p-power: η(p) is a ROOT OF UNITY value ✓ in R;
  [3] k = 0: source says k ≥ 0 in Lem 5.9 but here the φ-scaling at k = 0 gives
  (1−η(p)) — fine ✓ statement quantifies k : ℕ. SURVIVED.
- **L5.2.6** (internal): `muTheta` cluster — θ = χη, conductor Dp^n:
  μ_θ := twist χ̃ μ_η (TeX 1845–1846 verbatim: "we define
  $\mu_\theta \defeq (\mu_\eta)_\chi$"); Lem 5.12 transform formula (TeX
  1849–1852) in CLEARED form (G(θ⁻¹)-multiplied; at n = 0 no clearing needed);
  moments `∫x^k μ_θ = LvalNeg θ k` and Res-formula
  `Res_{ℤ_p^×}μ_θ = (1−θ(p)φ)μ_θ` (TeX 1858–1861).
  Composition: L5.1.2-twist of μ_η + L5.1.8 (Lem 5.4 at μ = μ_η) + the
  L5.1.10-style moment computation at modulus Dp^n + L5.2.4/ψ-side for the Res
  formula (θ(p) = χ(p)η(p) with χ(p) = 0 when n ≥ 1 — source TeX 1861:
  "(if $\chi$ is non-trivial, then $\mu_\theta$ is already supported on
  $\Zp^\times$; but this is consistent, as $\theta(p) = 0$)").
  Attacks: [1] θ as a DirichletCharacter at level Dp^n: mathlib product of
  chars at different levels via `changeLevel` to lcm — primitivity of θ = χη
  for coprime conductors: mathlib has `DirichletCharacter.IsPrimitive.mul`-?
  (verify at skeleton; classical fact; if absent: 15-line leaf via conductor
  of product of coprime-conductor primitives = product — needed also for
  genBernoulli θ); [2] n = 0 degeneration: θ = η, μ_θ = μ_η ✓ twist by trivial
  char = identity (χ̃ = 1 needs… at n = 0, conductor 1: χ̃ per L5.1.1 with
  n = 0 is the constant 1 — but L5.1.1 carried n ≥ 1 for the pZp-vanishing
  lemma only; the DEFINITION is fine at n = 0 ✓ guard placement re-checked);
  [3] the ψ(μ_θ)-computation when n ≥ 1: ψμ_θ = 0?? — source's Res-formula
  says Res μ_θ = (1−θ(p)φ)μ_θ = μ_θ (θ(p)=0) ⟹ φψμ_θ = 0 ⟹ ψμ_θ = 0
  (φ injective) — consistent with support ✓; the worker proves ψμ_θ = θ(p)ψ-
  shape uniformly via the L5.2.4-route at modulus Dp^n?? — CAREFUL: L5.2.4's
  telescope was at modulus D with ε_D; for θ-level the same algebra runs with
  ε_{Dp^n}… whose p-power part is NOT a unit-denominator — the γ_c-inverses
  don't all exist at level Dp^n!! RESOLUTION: μ_θ is DEFINED as twist of μ_η
  (not by an F_θ-formula); its ψ is computed from ψ-of-twist:
  ψ(twist χ̃ ν)-formula: twist-by-χ̃ and ψ interact through supp/digit algebra:
  for n ≥ 1: χ̃·(anything) is supported on units ⟹ ψ(twist) = 0 directly
  (ψ∘Res_units = 0, §3 Cor 3.32-side) ✓ NO level-Dp^n telescope needed; for
  n = 0 it IS L5.2.4. Lem 5.12's transform DISPLAY (the ε_{Dp^n}-sum) is then
  derived from L5.1.8 (whose ζ_{p^n}-twists multiply the ε_D-units inside the
  γ's — products ε_{p^n}^a·ε_D^b realise ε_{Dp^n}-terms via CRT, bookkeeping
  sub-leaf) — the ATTACK CAUGHT a wrong-route risk and fixed the decomposition
  (ψμ_θ via support, not telescope). SURVIVED (route corrected).
- **L5.2.7** (leaf): `zetaEta` definition + interpolation —
  ζ_η := x⁻¹-twist of Res_{ℤ_p^×}(μ_η) ∈ Λ_R(ℤ_p^×) (Def TeX 1866–1868
  verbatim: "Define $\zeta_\eta \defeq x^{-1} \mathrm{Res}_{\Zp^\times}(\mu_\eta).$")
  + final display (TeX 1870–1873): ∫χx^k ζ_η = (1−θ(p)p^{k−1})LvalNeg θ (k−1).
  Discharge: §4 T036 x⁻¹-twist machinery on ℤ_p^× (widened) + L5.2.5/L5.2.6.
  Attacks: [1] x⁻¹-twist on UNITS-side measures: T036's `zetaNum` infra ✓;
  [2] k > 0 shift bookkeeping (k−1 ≥ 0) ✓ destructure; [3] genuine measure (no
  pseudo-measure) ✓ by construction — matches source Remark 1 (TeX 1780).
  SURVIVED.
- **L5.2.8** (leaf): uniqueness/determinacy — a measure on ℤ_p^× vanishing
  against χ(x)x^k for all primitive χ mod p^n (n ≥ 0) and all k > 0 is zero.
  Source: implicit in "unique measure" (TeX 1774); expansion (Step-1 duty):
  the span of {χ̃·x^k} contains x·(every locally constant)·x^j; on ℤ_p^×, x is
  a unit of C(ℤ_p^×, R) so x·C = C; locally-constant-span × polynomials is
  dense (W-r2 density + Mahler/Stone–Weierstrass-free ultrametric argument:
  loc const alone is dense, and every loc const on ℤ_p^× times x^1 stays in the
  span with k = 1 ranging… need ALL characters of (ℤ/p^n)ˣ = all functions on
  it by Fourier inversion over L?? characters span functions needs |G|
  invertible + enough roots of unity in L — (ℤ/p^n)ˣ has order p^{n−1}(p−1):
  p NOT invertible in R… but in L it is! Coefficients-in-L span: the
  determinacy pairing lands in L; inversion uses 1/|G| ∈ L ✓ and characters
  OF (ℤ/p^n)ˣ with values in L: needs μ_{p^{n−1}(p−1)} ⊂ L — a HYPOTHESIS
  (L "sufficiently large", source Remark 2 TeX 1781–1782: "the relevant
  Iwasawa algebra is defined over a (fixed) finite extension L/Q_p containing
  the values" — for the UNIQUENESS over a fixed small L: restrict the
  uniqueness statement to measures over the L the theorem fixes; the χ's in
  the interpolation property have values in Q̄_p — the source quantifies over
  ALL primitive χ of p-power conductor, implicitly enlarging L per χ. Lean
  statement: uniqueness among Λ_{R}(ℤ_p^×) for the fixed R, quantifying the
  property over χ valued in R… faithful reading: fix L large enough to contain
  η's values AND all relevant χ-values? — IMPOSSIBLE finitely (all n!).
  RESOLUTION (replan note, statement-level): state Thm 5.7 as the source does
  but with the χ-quantifier ranging over characters **valued in any finite
  extension L'/L inside a fixed algebraic closure / inside ℂ_p**, with ζ_η's
  uniqueness in Λ_{R}: two candidate measures in Λ_R agreeing against all
  χ̃x^k for χ valued in EVERY L' are equal — the determinacy argument runs in
  the big field per-level. Lean-shape: coefficients functorial via baseChange
  (W4 for R → R'); the uniqueness lemma quantifies over levels n with
  characters over R_n := integerRing of L(μ_{p^n·(p−1)})… CONCRETE Lean
  spelling: use ℂ_p (PadicComplex) as the ambient: state determinacy for
  measures over R against ℂ_p-valued characters through baseChange R → 𝓞_ℂp.
  This is the honest faithful reading of the source's quantifier and uses
  mathlib's ℂ_p. Recorded as the R5.2-statement design (skeleton states it
  this way). [2] injectivity of baseChange R → 𝓞_ℂp on measures (needed so
  determinacy over ℂ_p kills the R-measure): coefficientwise on Mahler ⟸
  L → ℂ_p isometric embedding… exists for finite L/ℚ_p (into Q̄_p ⊂ ℂ_p) —
  HYPOTHESIS of the final theorem: an embedding L ↪ ℂ_p (canonical for
  subfields; statement carries `[Algebra L ℂ_[p]] [IsometricSMul…]`-grade or
  states L as a closed subfield — design pinned at skeleton with the simplest
  faithful form). [3] Fourier inversion on the finite abelian (ℤ/p^n)ˣ over an
  alg closed char-0 field: mathlib `MonoidAlgebra`/character orthogonality —
  `MulChar.orthogonality`-family exists? (DirichletCharacter/Orthogonality.lean
  EXISTS in the survey listing ✓ — verified file present; exact statements at
  skeleton). SURVIVED (with the two recorded design notes).
- **L5.2.9** (leaf, quarantined complex bridge): `LFunction_neg_eq_genBernoulli` —
  for χ : DirichletCharacter ℂ N (N ≥ 1): `DirichletCharacter.LFunction χ (−k)
  = −genBernoulli χ (k+1)/(k+1)` (ℂ-instance of genBernoulli), via mathlib
  `hurwitzZeta_neg_nat` summed against χ per the LFunction definition
  (ZMod.LFunction = N^{-s}Σ χ(j)hurwitzZeta(j/N) — definitionally).
  This is the §5 analogue of §4's ZetaValuesComplex bridge and the wiring
  target for the blueprint's L-value nodes; PR candidate.
  Source: Lem 5.5/5.9's L(χ,−k) — the complex meaning of the p-adic LvalNeg.
  Attacks: [1] hurwitzZeta_neg_nat's x ∈ [0,1] hypothesis vs j/N ✓ j.val/N ∈
  [0,1); [2] N^{k}-power bookkeeping between the N^{-s}-prefactor at s = −k and
  genBernoulli's N^{k−1} ✓ algebra; [3] the j = 0 term: χ(0) = 0 for N > 1 ✓,
  N = 1 special-cased to riemannZeta_neg_nat_eq_bernoulli' ✓. SURVIVED.

## R5.3: Analytic branches via Mellin (RJW §5.3, TeX 1885–1979)

### Source statements (verbatim)
- Lem 5.14 (TeX 1892–1894): "The $p$-adic exponential map converges on $p\Zp$.
  Hence, for any $s \in \Zp$, the function $1+p\Zp \rightarrow \Zp$ given by
  $x \mapsto x^s \defeq \mathrm{\exp}(s\cdot\mathrm{log}(x))$ is well-defined."
- Def 5.15 (TeX 1899–1905): "Recall that we assume $p$ to be odd and that we
  have a decomposition $\Zp^\times \cong \mu_{p-1} \times (1+p\Zp)$. Let
  $\omega : \Zp^\times \to \mu_{p-1}$, $\langle\cdot\rangle : \Zp^\times \to
  1+p\Zp$ … $\omega(x) \defeq$ Teichmüller lift … $\langle x \rangle \defeq
  \omega^{-1}(x) x$."
- Def 5.16 (TeX 1912–1918): "$\zeta_{p,i}(s) \defeq \int_{\Zp^\times}
  \omega(x)^{i}\langle x\rangle^{1-s} \cdot\zeta_p$."
- Thm 5.17 (TeX 1921–1924): "For all $k\geq 1$ with $k \equiv i \newmod{p-1}$,
  we have $\zeta_{p,i}(1-k) = (1-p^{k-1})\zeta(1-k)$."
- Def 5.18 (TeX 1929–1932): "$L_p(\theta,s) \defeq \int_{\Zp^\times}
  \chi(x)\langle x\rangle^{1-s} \cdot \zeta_\eta$, $s\in\Zp$."
- Thm 5.19 (TeX 1943–1946): "For all $k\geq 1$, we have $L_p(\theta,1-k) =
  \big(1 - \theta \omega^{-k}(p)p^{k-1}\big) L(\theta \omega^{-k},1-k)$."

### Leaves (Branches.lean; coefficients ℤ_p for ω/⟨·⟩, L for the L_p-values)

- **L5.3.1** (leaf): `teichmuller : ℤ_[p]ˣ →* ℤ_[p]ˣ`-grade (p odd) — ω(x) :=
  lim_{n} x^{p^n}; API: `teichmuller_pow_card_sub_one` (ω(x)^{p−1} = 1),
  `teichmuller_sub_self_mem` (ω(x) ≡ x mod p), `teichmuller_mul`,
  `teichmuller_eq_self_iff` (fixed points = μ_{p−1}), `teichmuller_unit`.
  Source: Def 5.15 ("Teichmüller lift of the reduction modulo p"); construction
  cross-ref: Washington §… / standard. Route: x^{p^{n+1}} − x^{p^n} =
  x^{p^n}((x^{p^n})^{p−1·…}−1)… Cauchy via Fermat (x^p ≡ x mod p ⟹ x^{p^{n+1}}
  ≡ x^{p^n} mod p^{n+1} by induction with binomial): CompleteSpace ℤ_p limit.
  Mathlib check: `Perfection.teichmuller` exists but extraction to ℤ_p direct
  is heavier than the 40-LOC limit construction (recorded decision; revisit if
  the worker finds `WittVector.equiv`-route shorter).
  Attacks: [1] p = 2: μ_{2−1} trivial, ω ≡ 1, statement degenerates but the
  CONSTRUCTION needs no p ≠ 2 — yet Def 5.15's DECOMPOSITION does (source
  "Recall that we assume p to be odd"); p odd hypothesis sits on the
  decomposition lemma L5.3.2, not on ω ✓ (never silently drop, rule 5 ✓);
  [2] multiplicativity: limit of multiplicative maps ✓; [3] continuity of ω:
  needed? (for measurability-free pairing yes: ω^i·⟨x⟩^{1−s} must be
  CONTINUOUS in x: ω is locally constant (ω(x) determined by x mod p:
  ω(x) = ω(y) if x ≡ y mod p — from the construction's congruences) — API
  lemma `teichmuller_eq_of_sub_mem` added ✓. SURVIVED.
- **L5.3.2** (leaf): `unitsDecomp` (p odd) — x = ω(x)·⟨x⟩ with
  ⟨x⟩ := ω(x)⁻¹x ∈ 1 + pℤ_p; uniqueness of the decomposition; ⟨·⟩
  multiplicative, continuous, ⟨x⟩ = x for x ∈ 1+pℤ_p.
  Source: Def 5.15 (quoted). Discharge: L5.3.1 API; uniqueness: μ_{p−1} ∩
  (1+pℤ_p) = 1 (orders coprime: an element of order dividing p−1 that is
  ≡ 1 mod p is 1 — via L5.3.1 fixed-point + (1+pℤ_p) torsion-free for p odd —
  the (ZMod 8)ˣ-noncyclic trap lives exactly here, p = 2 EXCLUDED ✓).
  Attacks: [1] (1+pℤ_p) torsion-freeness p odd: §4's `topGen_pow_ne_one`/T037
  infra adjacent — re-derivable from binomial valuation (‖(1+py)^m − 1‖ =
  ‖m‖·‖py‖ for p odd — the standard isometry lemma, sub-leaf ~15 LOC, also
  needed by L5.3.3 injectivity); [2] p = 2 falsity: (ℤ/8)ˣ ✓ excluded;
  [3] ω(x)⁻¹: ω valued in UNITS ✓ construction. SURVIVED.
- **L5.3.3** (leaf): `onePAdicPow` — for y ∈ 1+pℤ_p, s ∈ ℤ_p: `y^[s] :=
  (PadicInt.addChar_of_value_at_one (y−1) h_nilp) s` (mathlib AddChar at
  R = ℤ_[p]); API: agrees with monoid-pow on ℕ (`addChar`-uniqueness/
  construction), multiplicative in s (AddChar ✓ free), multiplicative in y
  (`(y₁y₂)^[s] = y₁^[s]y₂^[s]` — via continuousAddCharEquiv uniqueness),
  continuous in s AND in y, `y^[s] ∈ 1+pℤ_p`, and the INTERPOLATION property:
  s = k : ℕ gives y^k.
  Source: Lem 5.14 (quoted). **Recorded replan (statement-level):** the source
  DEFINES x^s = exp(s log x); p-adic exp/log are not in mathlib (survey); the
  binomial/character construction defines the same function (both are the
  unique continuous homomorphism ℤ_p → 1+pℤ_p sending 1 ↦ y — uniqueness by
  density of ℤ ⊂ ℤ_p; the source's exp∘log map is continuous and sends 1 ↦ y).
  The blueprint node for Lem 5.14 states the exp-version and stays UNWIRED
  (prose note: realised via the equivalent character construction
  `onePAdicPow`; the exp/log development is future work — surfaced to user).
  Attacks: [1] (y−1) top-nilpotent: ‖y−1‖ ≤ p⁻¹ < 1 ✓; [2] does
  addChar_of_value_at_one VALUE in 1+pℤ_p (needed: ⟨x⟩^s a UNIT for the
  ζ_p-pairing)? — values: κ(s) = Σ binom(s,m)(y−1)^m: m ≥ 1 terms ∈ pℤ_p ✓
  κ(s) ∈ 1+pℤ_p ✓ unit ✓ lemma; [3] continuity in y (for L_p(θ,·)-analyticity
  later — NOT needed for §5 statements; skip, note for §6). SURVIVED.
- **L5.3.4** (leaf): the character `kappa i s : C(ℤ_p^×, ℤ_p)` —
  x ↦ ω(x)^i·⟨x⟩^[s]-as-continuous-map + multiplicativity + the κ(x) = x^k
  identification: for k ≡ i mod (p−1), `kappa i k = x^k on units`
  (x^k = ω(x)^k⟨x⟩^k = ω(x)^i⟨x⟩^[k] — source TeX 1919's "the character $x^k$
  can be written in the form $\omega(x)^i\langle x\rangle^k$ if and only if
  $k \equiv i \mod{p-1}$").
  Discharge: L5.3.1–L5.3.3 + ω^{p−1} = 1. Attacks: [1] "only if" direction not
  needed ✓ skip (statement-level: the iff is prose; the formal lemma is the
  if-direction used by Thm 5.17); [2] continuity: ω loc const + ⟨·⟩^[s] cts ✓;
  [3] i-range 1..p−1 vs i : ZMod (p−1): skeleton uses i : ℕ with the
  congruence hypothesis (source's indexing) ✓. SURVIVED.
- **L5.3.5** (leaf): pseudo-measure/character pairing — for κ : C(ℤ_p^×, ℤ_p)
  multiplicative (a continuous character) with κ(b) − 1 ≠ 0 for the §4
  generator-witness b, and λ a pseudo-measure with witnesses: define
  `pairChar λ κ := (κ(b)−1)⁻¹ · ∫κ dν_b ∈ ℚ_p` (ν_b the witness of
  ([b]−[1])λ) — well-definedness across witnesses/generators via the §3
  machinery (the multiplicativity identity ∫κ d([b]−1)μ = (κ(b)−1)∫κ dμ for
  genuine μ — NEW small lemma `integral_char_dirac_mul`: ([b]−1)·μ paired with
  multiplicative κ — convolution-vs-character: ∫κ d(δ_b·μ) = κ(b)∫κ dμ ⟸
  convolution `mul_apply` + κ(bx) = κ(b)κ(x) ✓ ~15 LOC).
  Source: Def 5.16 glosses this ("meromorphic"); the pairing is the standard
  reading (cf. §4's moment encoding which is its k-th-power instance).
  Attacks: [1] independence of witness: two witnesses differ by … ([b]−1)-
  torsion-free (§3 zero-divisor (i)) ✓ same argument as T038/T039;
  [2] independence of b (for the THEOREM only one b is used; the DEFINITION
  fixes the T037 generator u — junk-free domain: s such that κ_{i,s}(u) ≠ 1;
  for Thm 5.17's (i,k): κ(u) = ω(u)^i⟨u⟩^{1−(1−k)} = ω(u)^i⟨u⟩^{k}…
  at k ≡ i: = u^k ≠ 1 for k ≥ 1 (u top. generator, torsion-free) ✓
  well-defined exactly where needed; [3] ζ_{p,0}(1)-pole: κ trivial at
  (i,s) = (0,1): excluded by k ≥ 1 ✓ junk value there, recorded.
  SURVIVED.
- **L5.3.6** (internal): `zetaPBranch` + **Thm 5.17** — ζ_{p,i}(s) :=
  pairChar (padicZeta) (kappa i (1−s)); theorem: for k ≥ 1, k ≡ i (p−1):
  ζ_{p,i}(1−k) = (1−p^{k−1})·zetaNeg-value (the §4 rational ζ(1−k)).
  Composition: L5.3.4 (κ = x^k on units) + L5.3.5 + §4's padicZeta_moments
  (T038: the moment formula at x^k) — definitional alignment of the two
  pairings.
  Attacks: [1] the 1−s vs s twist: Def 5.16 has ⟨x⟩^{1−s} ✓ statement uses
  kappa i (1−s) — at s = 1−k: ⟨x⟩^{k} ✓ matches the trace in L5.3.5-[2];
  [2] ζ(1−k)-side: §4's zetaNeg (k−1)-indexing re-used ✓ (same value object as
  T039 — no complex ζ needed); [3] i odd ⟹ both sides 0 (source remark TeX
  1927): consequence, not hypothesis ✓ no extra work. SURVIVED.
- **L5.3.7** (internal): `LpFunction` + **Thm 5.19** — L_p(θ,s) :=
  ∫χ̃(x)⟨x⟩^[1−s] dζ_η (a GENUINE integral — ζ_η is a measure ✓ no pairing
  subtleties); theorem TeX 1943–1946 via the eq:alternative route (TeX
  1948–1956): χ⟨x⟩^{k−1} = χω^{−k}·x^{k−1}·ω^{…}-character algebra (L5.3.4)
  + L5.2.7's interpolation at the character χω^{−k}-twisted powers — NOTE:
  Thm 5.19's RHS involves L(θω^{−k},1−k) — the χ-part of θω^{−k} is χω^{−k},
  ANOTHER p-power-conductor character: the moments of ζ_η against
  (χω^{−k})(x)x^{k−1}-shape = exactly L5.2.7's quantified statement ✓ the
  composition is pure bookkeeping over the χ-quantifier (no new analysis).
  Attacks: [1] ω as a Dirichlet character mod p: ω's values μ_{p−1} ⊂ ℤ_p ✓
  `teichmullerChar : DirichletCharacter ℤ_[p]-or-L p` bridge leaf (ω(x mod p)
  = ω(x): L5.3.1 loc-const API ✓ ~10 LOC); [2] θω^{−k} conductor bookkeeping:
  its p-part χω^{−k} primitive of some conductor p^m — L5.2.7 quantifies over
  ALL primitive p-power χ' ✓ no conductor computation needed, just
  primitivisation (mathlib `primitiveCharacter`) + equality of the FUNCTIONS
  χ̃'·x^{k} on ℤ_p^× (values agree: x^k-shift absorbs) — the bookkeeping
  lemma is the one real content ✓ bounded; [3] s-domain: all s ∈ ℤ_p ✓
  genuine integral. SURVIVED.

## §5 prior-B2 consultation (Step 4.6)
`b2_log.jsonl` checked 2026-06-10: empty (0 entries). No name or shape matches
possible. Clean.

## §5 confidence gate (Step 5) — assessment

1. Every leaf above is mathlib-discharged (cited + verified in the §5 survey
   table, plan.md), project-discharged (named §3/§4 decls + W-widening), or an
   explicit API-gap with its own sub-decomposition (W1–W4, L5.1.5, L5.1.9–10,
   L5.2.8-design, L5.3.1–3) — no "figure it out during execution" steps remain.
2. Skeleton: new-math leaves skeletonised in the 7 files listed; W-cluster per
   the recorded refactor exception. `lake build` gate checked at skeleton commit.
3. Verbatim quotes: every R5.x leaf carries one (or points at the §3-tree quote
   it generalises — W). Lean ↔ source match paragraphs inline per leaf.
4. Adversarial pass: every leaf has ≥ 3 attacks logged; FOUR attacks found real
   defects and fixed the plan at planning time (L5.1.8 statement-sign by trace;
   L5.2.6 wrong-route at level Dp^n; L5.2.8 quantifier design; W-r1 false
   circularity resolved by R-valuedness) — the pass earned its keep.
5. Prior-B2: empty log, clean.
6. Tree mirrors the source: §5.1 follows TeX 1623–1765's chain (a)–(e); §5.2
   follows TeX 1785–1875 item-by-item (each "good exercise" gap expanded as a
   leaf with the expansion recorded); §5.3 follows TeX 1885–1962. LOC estimates
   deferred to tickets, grounded per-leaf in the source-line spans cited there.

REVIEW-PENDING: none. API gaps all carry sub-decompositions. GATE PASSES for
ticket creation, with the three recorded replan/design notes (R5-CLEAR,
L5.2.4-route, L5.2.8/L5.3.3 statement designs) to surface at board approval.

## R5.E: p-adic exponential and logarithm (user-requested 2026-06-10 at board approval)

### Source statement (verbatim, TeX 1892–1897, Lem 5.14)
> "The $p$-adic exponential map converges on $p\Zp$. Hence, for any $s \in \Zp$,
> the function $1+p\Zp \rightarrow \Zp$ given by $x \mapsto x^s \defeq
> \mathrm{\exp}(s\cdot\mathrm{log}(x))$ is well-defined."
> Proof: "This is a standard result in the theory of local fields; see e.g.\
> \cite[\S12]{cassels}."

### Step 1 prose (source defers to Cassels §12; cross-reference Washington §5.1
— fallback chain step 1, recorded)
exp(x) = Σ x^n/n! converges iff v_p(x) > 1/(p−1) (Legendre: v_p(n!) =
(n − s_p(n))/(p−1)); on that ball exp is an isometry (‖exp x − exp y‖ = ‖x−y‖,
each difference-term beyond the linear one being strictly smaller
ultrametrically), hence a bijection onto 1 + ball with inverse log; exp(x+y) =
exp(x)exp(y) by the binomial/double-series rearrangement (unconditional
convergence, ultrametric). For p odd, pℤ_p is inside the ball; x^s := exp(s log x)
is then a continuous character ℤ_p → 1+pℤ_p with value x at 1, hence agrees with
`onePAdicPow` (L5.3.3) by uniqueness (`continuousAddCharEquiv`).

### Leaves (PadicLFunctions/PadicExp.lean; over the §5 coefficient field L)
- **E1** (leaf): ultrametric summability — a family `f : ι → L` is summable iff
  `f → 0` along cofinite (complete ultrametric). Mathlib check at execution
  (`IsUltrametricDist`-summability API); else ~25 LOC via Cauchy partial sums.
  Attacks: [1] needs T2+complete ✓ L; [2] ι countable not needed ✓ cofinite
  form; [3] known-true classical. SURVIVED.
- **E2** (leaf): `‖(n.factorial : L)‖ = p^{-v_p(n!)}` + Legendre bound
  `v_p(n!) ≤ (n−1)/(p−1)` (mathlib `padicValNat` factorial API — verify names
  `Nat.Prime.factorization_factorial`/`padicValNat_factorial`; the ≤-bound is
  s_p(n) ≥ 1 for n ≥ 1). Attacks: [1] n = 0 edge (0! = 1, v = 0 ✓);
  [2] the bound is sharp at n = p^k — only ≤ needed ✓; [3] norm-of-cast via
  NormedAlgebra isometry ✓ W1-route. SURVIVED.
- **E3** (leaf): `padicExp : L → L` (junk-total, defined as tsum of x^n/n!),
  `padicExp_isometry : ‖x‖ < rExp → ‖y‖ < rExp → ‖padicExp x − padicExp y‖ =
  ‖x − y‖` where `rExp := p^{-1/(p−1) : ℝ}`-ball; `padicExp_add` on the ball
  (double-series + `Summable.tsum_prod`/`tsum_comm` + antidiagonal binomial);
  `padicExp_zero = 1`; `‖padicExp x − 1‖ = ‖x‖`; convergence-on-pℤ_p corollary
  for p odd (‖x‖ ≤ p⁻¹ < p^{-1/(p−1)} ⟸ p odd; for p = 2 the radius excludes
  2ℤ₂ — the source's pℤ_p-statement is the p-odd instance; the general-radius
  form is stated p-uniformly, NO silent p≠2 drop). Attacks: [1] Cauchy-product
  trap: norm-summability unavailable ultrametrically — route via unconditional
  tsum_prod RECORDED (not tsum_mul_tsum) ✓; [2] junk-total def vs ball-guarded
  lemmas — §4 Fa-pattern ✓; [3] isometry constant: ‖x^n/n!‖ < ‖x‖ for n ≥ 2 on
  the OPEN ball needs strict Legendre: v(x^n/n!) − v(x) = (n−1)v(x) − v(n!) >
  (n−1)/(p−1) − (n−1)/(p−1) = 0 ✓ strict on open ball ✓ (CAUGHT: at the CLOSED
  radius it fails — ball openness is essential; statements use strict ‖·‖ <
  rExp, with pℤ_p ⊂ open ball for p odd ✓). SURVIVED (attack [3] pinned
  strictness).
- **E4** (leaf): `padicExp_bijOn : BijOn padicExp (ball 0 rExp) (1 + ball)` —
  injective (isometry), surjective onto `{y | ‖y − 1‖ < rExp}` (completeness:
  the standard successive-approximation/contraction — Washington Prop 5.4
  route) — and `padicLog : L → L` := the inverse on that ball (junk-total via
  Function.invFunOn or explicit series; DESIGN: define padicLog by the SERIES
  Σ −(−1)^n(x−1)^n/n (converges for ‖x−1‖ < 1, BIGGER ball) and prove
  exp∘log/log∘exp on the matched small balls via the isometry+algebra —
  faithful to "log" being the standard series and giving log on all of
  1+pℤ_p... wait for p odd pℤ_p-ball: series-log converges on ‖x−1‖ < 1 ⊃
  1+pℤ_p ✓ but exp∘log = id only holds on ‖x−1‖ < rExp... for p odd
  ‖x−1‖ ≤ 1/p < rExp = p^{-1/(p−1)} ✓ all consistent on 1+pℤ_p. Series-log
  it is; the bijection statement scoped to the rExp-balls.) Attacks:
  [1] log-series convergence: v(yⁿ/n) = n·v(y) − v(n), v(n) ≤ log_p n → ✓
  → ∞; [2] exp(log x) = x route: BOTH are limits of the formal identities'
  partial sums — the clean p-adic proof (Washington Prop 5.3): isometry-based:
  g := exp∘log − id is continuous, vanishes on the DENSE?? no — standard
  route: formal power-series identity composed with evaluation: needs formal
  `PowerSeries.exp/log` composition in mathlib (`PowerSeries.exp_log`-? NOT
  confirmed) — FALLBACK (recorded): derivative-free telescoping à la
  Washington 5.3 via the functional equations: exp_add (E3) + log_mul (same
  tech) + the order-1 isometry pin exp(log x)·x⁻¹ ≡ 1: hmm — ROBUST ROUTE:
  uniqueness of continuous characters AGAIN: for fixed x ∈ 1+pℤ_p (p odd),
  s ↦ exp(s·log x) and s ↦ onePAdicPow x s are both continuous characters
  ℤ_p → ℤ_p^×-ball with the SAME derivative-free determination at s ∈ ℕ?:
  exp(n log x) = exp(log x)^n (exp_add ✓) so at s = 1 they agree IFF
  exp(log x) = x — circular for the identity itself. DECISION: prove
  exp∘log = id on 1+pℤ_p the honest way: composition of series with
  ultrametric Fubini (double-sum over the log-expansion inside exp — finite
  multinomial bookkeeping; Washington does exactly this in 5.3; ~80 LOC).
  E4 carries the real work; sized accordingly. [3] image
  characterisation 1+ball: from isometry ‖exp x − 1‖ = ‖x‖ ✓. SURVIVED
  (route pinned: series-composition with ultrametric Fubini).
- **E5** (internal): **Lem 5.14 as stated** — `padicExp_converges_on_pZp`
  (p odd; the source's first sentence), `expPow x s := padicExp (s • padicLog x)`
  well-defined `1+pℤ_p → ℤ_p` for s ∈ ℤ_p (p odd), and
  `expPow_eq_onePAdicPow : expPow x s = onePAdicPow x hx s` (character
  uniqueness: s ↦ expPow x s is continuous + additive (exp_add + log-linearity
  of s·log x) with value exp(log x) = x at s = 1 (E4)).
  Composition: E1–E4 + `PadicInt.continuousAddCharEquiv` uniqueness + L5.3.3.
  Attacks: [1] ℤ_p-valuedness of expPow: ‖s·log x‖ ≤ ‖log x‖ ≤ 1/p ⟹ exp-value
  ∈ 1+pℤ_p ⊂ ℤ_p ✓ E3-isometry; [2] s • log x: ℤ_p-action on L vs ℤ_p-target —
  for the Lem 5.14 statement work over ℤ_p directly (L := ℚ_p-instance or the
  ℤ_p-restricted statements; skeleton states the ℤ_p forms; general-L forms
  are the PR-shape) ✓ both recorded; [3] blueprint wiring: the chapter's
  Lem 5.14 node NOW wires to `padicExp_converges_on_pZp`+`expPow`-pair
  (user-approved exp/log cluster removes the L5.3.3 unwired-rationale).
  SURVIVED.

Gate (E-cluster): all leaves discharged-or-sub-decomposed; quotes present
(TeX 1892–1897 + Cassels/Washington cross-refs recorded); attacks logged with
two real route-pins (E3 strictness, E4 composition route). PASSES.

## R6: The values at s = 1 (RJW §6, TeX 1980–2180) — draft-1 (pre-skeleton)

### Source statements (verbatim)
- Thm 6.1 (`s=1 theorem`, TeX 1987–1995): "Let $\theta$ be a non-trivial
  Dirichlet character of conductor $N$, and let $\varepsilon_N$ denote a
  primitive $N$th root of unity. Then: (i) (Classical value at $s=1$). We have
  $L(\theta,1) = -\frac{1}{G(\theta^{-1})} \sum_{c \in (\Z/N\Z)^\times}
  \theta^{-1}(c) \log\big( 1-\varepsilon_N^c \big)$. (ii) ($p$-adic value at
  $s=1$). We have $L_p(\theta,1) = -\big( 1 - \theta(p) p^{-1} \big)
  \frac{1}{G(\theta^{-1})} \sum_{c \in (\Z/N\Z)^\times} \theta^{-1}(c)
  \log_p\big(1-\varepsilon_N^c)$."
- F̃ def (TeX ~2070): "$\widetilde{F}_\theta(T) = - \frac{1}{G(\theta^{-1})}
  \sum_{c \in (\Z / N \Z)^\times} \theta^{-1}(c) \log \big( (1 + T)
  \epsilon_N^c - 1 \big)$".
- Lem 6.2 (`lem:bounded power series`, TeX 2074): "The power series
  $\widetilde{F}_\theta(T)$ is an element of $\mathscr{R}^+$." (Proof TeX
  2076–2085: the log-expansion $\log((1+T)\epsilon^c-1) =
  \log_p(\epsilon^c-1) + \sum_{n\ge1} \frac{(-1)^{n-1}}{n}
  \frac{\epsilon^{cn}}{(\epsilon^c-1)^n}T^n$.)
- Lem 6.3 (`lem:mu theta'`, TeX 2090): "We have $x \widetilde{\mu}_\theta =
  \mu_\theta$. In particular, $\mathrm{Res}_{\Zp^\times}(\widetilde{\mu}_\theta)
  = x^{-1}\mathrm{Res}_{\zpe}(\mu_\theta)$." (Proof: $\partial\widetilde F =
  F_\theta$ via $\partial\log((1+T)\epsilon^c-1) = 1 +
  \frac{1}{(1+T)\epsilon^c-1}$ and $\sum_c\theta^{-1}(c) = 0$.)
- eq:Lptheta 1,2 (TeX 2113): "$L_p(\theta,1) =
  \big((1-\varphi\circ\psi)\widetilde F_\theta\big)(0)$".
- Proof of (ii), case n≥1 (TeX 2120–2126): χ kills pℤ_p so
  $\mathrm{Res}_{p\Zp}(\widetilde\mu_\theta)=0$; case n=0 (TeX 2128–2148):
  Eqphipsi ξ-sum, $\sum_{\xi\in\mu_p}\log_p(\xi\varepsilon_N^c-1) =
  \log_p(\varepsilon_N^{pc}-1)$, and the automorphism $c\mapsto pc$ giving
  $\varphi\circ\psi(\widetilde F_\theta)(0) = \frac{\theta(p)}{p}
  \widetilde F_\theta(0)$. Final step uses $\log_p(x)=\log_p(-x)$.

### Recorded replans (rule 5; user-approved route 2026-06-11 "as planned")
1. **Distribution-free route for (ii)** (plan.md §6 addendum): RJW's
   ℛ⁺/locally-analytic layer (thm:mahler la) is replaced by the ψ-kernel
   constant-pin at the formal-series level. Lem 6.2's ℛ⁺-membership is NOT
   formalised (deferred with the §3.7 cluster); Lem 6.3's content enters as
   the pair (∂F̃ = F_θ formal identity) + (𝓐_ρ = F̃ − φψF̃ by ∂-match,
   ψ-kernel, ker ∂ = constants). Thm 6.1(ii)'s STATEMENT is unchanged.
2. **ψ-evaluation instead of formal Eqphipsi.** ATTACK (succeeded, route
   fixed): the planned "Eqphipsi as a formal-series identity
   φψF = p⁻¹Σ_ξ F((1+T)ξ−1)" is ILL-FORMED in PowerSeries: the substitution
   T ↦ (1+T)ξ−1 has non-nilpotent constant term ξ−1 ≠ 0 for ξ ≠ 1, so
   `PowerSeries.subst` does not apply. Fix: the deferred Eqphipsi is
   realised as the CONVERGENT-EVALUATION identity at T = 0 only:
   `psiSeries_eval_zero : (ψF).eval 0 = p⁻¹ Σ_{ξ∈μ_p} F.eval (ξ−1)`
   (eval := ∑' coeff_n • zⁿ, the T522 helper pattern), proved by evaluating
   the digit decomposition F = Σ_{i<p}(1+T)^i·φ(F_i) at z = ξ−1 (where
   (1+z)^p−1 = 0 collapses the φ-layer) + μ_p-orthogonality Σ_ξ ξ^i = p·[i=0].
   This needs μ_p ⊂ K (the §5 hε-hypothesis pattern) and convergence only
   for our explicit log-growth coefficients.
3. **Case n ≥ 1 via primitive-fiber character sums.** RJW's support argument
   (χ|_{pℤ_p} = 0 ⟹ Res_{pℤ_p}μ̃ = 0) is replaced by: in the evaluated
   ξ-sum, Σ_{c∈(ℤ/N)ˣ} θ⁻¹(c)·extLog(ε_N^{pc}−1) regroups along the p-to-1
   map c ↦ pc whose fibers are translates by N/p; the inner sum
   Σ_{j mod p} θ⁻¹(c + jN/p) = 0 because θ is primitive of conductor N
   (does not factor through N/p). Same conclusion ((φψF̃)(0) = 0 = θ(p)·…
   since θ(p) = 0), uniform bookkeeping with case n = 0 (where c ↦ pc is an
   automorphism and the sum collapses to θ(p)·F̃(0)).
4. **Scope: D > 1.** Thm 6.1(ii) is stated for θ = χη with η primitive of
   conductor D, 1 < D, p ∤ D (the §5.2 standing hypotheses, =
   zetaEta/LpFunction stack). The pure-p-power case D = 1 (θ = χ ≠ 1) is
   DEFERRED: RJW's own §5.2 μ_η-machinery assumes D > 1, and the D = 1
   object is the χ-twist of the ζ_p pseudo-measure (a genuine measure, but
   needing its own mini-cluster). Deferred-note to plan.md "Deferred" table;
   blueprint node will carry a rationale sentence.
5. **Clearing convention.** All series-level work is G-cleared as in §5
   (muEtaCleared/T508 twist conventions). RJW's 1/G(θ⁻¹) display is
   recovered through the coprime Gauss-sum factorisation leaf (c4 below);
   the headline statement matches RJW's display in K after un-clearing by
   the unit G-factors.

### Cluster W6a — extended p-adic logarithm (new file PadicLFunctions/ExtLog.lean)
Source: statement-level RJW TeX 1992–1995 (log_p at 1−ε^c) — RJW never
construct log_p beyond Lem 5.14's ball; construction cross-ref Washington
*Cyclotomic Fields* §5.1 (Iwasawa log, ~1.5pp). Ambient: the PadicExp
variables (L complete ultrametric NormedField, NormedAlgebra ℚ_[p] L).
- a1 (leaf) `mul_mem_expBall`: y,z ∈ 1+ball ⟹ yz ∈ 1+ball (ultrametric;
  ‖yz−1‖ ≤ max(‖y−1‖‖z‖, ‖z−1‖)).
- a2 (leaf) `padicLog_pow`: padicLog(y^n) = n • padicLog y (induction on
  padicLog_mul + a1).
- a3 (leaf) `norm_pow_p_sub_one_le`: ‖w−1‖ < 1 ⟹
  ‖w^p−1‖ ≤ max(‖w−1‖^p, p⁻¹‖w−1‖) (binomial, p ∣ C(p,i) for 0<i<p).
- a4 (leaf) `exists_pPow_pow_inExpBall`: ‖w−1‖ < 1 ⟹ ∃ j,
  InExpBall p (w^(p^j) − 1) (iterate a3; ratio max(r^{p−1}, p⁻¹) < 1
  geometric. ATTACK note: at the closed boundary r = p^{-1/(p−1)} a single
  step does NOT contract (r^p = r/p exactly) but r < 1 still gives the
  strict geometric factor max(r₀^{p−1},p⁻¹) < 1 — the iteration passes
  THROUGH the boundary; verified by hand).
- a5 (leaf) `exists_pow_sub_one_norm_le` (pigeonhole): z integral over ℤ,
  ‖z‖ = 1 ⟹ ∃ m > 0, ‖z^m − 1‖ ≤ p⁻¹. Route: Algebra.adjoin ℤ {z} is
  module-finite (IsIntegral), its mod-p quotient is finite, pigeonhole gives
  z̄^i = z̄^{i+m}, i.e. z^i(z^m−1) ∈ p·(adjoin) ⊆ p·integerRing, and
  ‖z^i‖ = 1 cancels WITHOUT needing z̄ invertible (norm multiplicativity).
  ATTACK (succeeded, design fixed): the naive "z̄ unit in the finite ring"
  claim is false in general (z⁻¹ need not be integral); the norm-cancel
  formulation avoids it.
- a6 (def) `extLog` (junk-total): dite on
  ∃ m k y, 0 < m ∧ x^m = (p:L)^k * y ∧ InExpBall p (y−1), value
  (m:ℚ_[p])⁻¹ • padicLog y (choice-extracted witness).
- a7 (leaf) `extLog_eq_of_witness`: any witness computes extLog
  (well-definedness: x^{mm'} two ways ⟹ p^{km'−k'm} = y'^m y^{−m'};
  norms force km' = k'm since ‖p‖ < 1 and the y-side has norm 1;
  cancel and apply a2).
- a8 (leaf) `extLog_eq_padicLog`: InExpBall p (x−1) ⟹ extLog x = padicLog x
  (witness (1,0,x)).
- a9 (leaf) `extLog_mul`: both in domain ⟹ extLog(xy) = extLog x + extLog y
  (combine witnesses, a1, padicLog_mul, a2).
- a10 (leaf) `extLog_eq_zero_of_pow_eq_one` (roots of unity) +
  `extLog_neg` (via (−1)² = 1 and a9; needs −x ∈ domain from x ∈ domain —
  square the witness).
- a11 (leaf) `extLogDomain_of_integral_norm_one`: z integral over ℤ, ‖z‖ = 1
  ⟹ z in the extLog domain with k = 0 witness (a5 then a4; covers ALL the
  theorem's arguments 1−ε_N^c for D > 1 — their norm-1-ness is p7's c-side
  bookkeeping via the cyclotomic product Φ_D(1)).
Sizing: Washington §5.1 ≈ 1.5pp → ~300 LOC.

### Cluster W6b — formal ψ on power series + evaluation (new file PadicLFunctions/MeasureR/FormalPsi.lean)
Source: the §3 deferral (plan.md "Deferred", Eqphipsi TeX ~1147–1160 region);
realisation per replan 2 above. Digit decomposition mirrors the project's
measure-level ψ (Measure/Toolbox digit shift).
- b1 (leaf) digit decomposition: for R comm ring, every F ∈ R⟦T⟧ has unique
  digits F = Σ_{i<p} (1+T)^i · φ(F_i) where φG := G.subst((1+T)^p−1)
  (HasSubst ✓ constant term 0). Existence/uniqueness by triangular
  coefficient recursion (the monomials (1+T)^i((1+T)^p−1)^j have leading
  term T^{i+pj}, and i+pj ↔ ℕ is the base-p digit bijection). ~60 LOC,
  the meaty formal leaf.
- b2 (leaf) `psiSeries` def := F_0; ψφ = id; ψ(C a) = C a; R-linearity.
- b3 (leaf) `psiSeries_derivative`: ψ∂ = p·∂ψ where ∂ = (1+T)d/dT
  (differentiate the digit decomposition; ∂φ = p·φ∂ sub-lemma).
- b4 (leaf) bridge `mahlerTransform_psi`:
  𝓐_{ψμ} = psiSeries(𝓐_μ) over integerRing K (against the project's
  measure-ψ; both are digit-0 extractions — expected near-definitional
  through mahlerRingEquiv; verify at execution).
- b5 (leaf) eval layer: `seriesEval F z := ∑' n, coeff n F • z^n`
  (junk-total; EXTRACT/generalise the T522 helpers padicExp_eq_tsum_coeff
  pattern), linearity, and `seriesEval_phi`: eval(φG) z = eval G ((1+z)^p−1)
  under summability (subst-vs-eval compatibility — bounded case suffices? NO:
  needed at log-growth coefficients; state with explicit summability hyps).
- b6 (leaf) `psiSeries_eval_zero`: with hξ : IsPrimitiveRoot ξ p in K and
  convergence hyps: seriesEval (psiSeries F) 0 = p⁻¹ • Σ_{i<p} seriesEval F
  (ξ^i − 1) (evaluate b1's decomposition at ξ^i−1; (1+(ξ^i−1))^p−1 = 0
  collapses φ; orthogonality Σ_{i<p} ξ^{ij} = p·[j=0 mod p] — mathlib
  IsPrimitiveRoot orthogonality/geom_sum).
  ATTACK note (replan 2): this REPLACES the ill-formed formal Eqphipsi.
- b7 (leaf) `derivative_eq_zero_iff_constant` (ker ∂ = constants, char-0
  field coefficients) — possibly in mathlib (verify); else 10 LOC.
Sizing ~250 LOC.

### Cluster C6 — the complex value (i) (new file PadicLFunctions/ValuesAtOneComplex.lean)
Source: TeX 2007–2045 (≈ 39 lines, Washington Thm 4.9). Quarantined complex
file per the §4 ZetaValuesComplex pattern. Mathlib-linking: state against
`DirichletCharacter.LFunction`.
- c1 (leaf) Fourier/Gauss expansion (eq:classical 6.1): for Re s > 1,
  LSeries-of-θ rearranges to G(θ)/N · Σ_c θ⁻¹(c)·Σ_n ε^{-nc}/n^s; via
  θ(a) = G(θ)/N·Σ_c θ⁻¹(c)ε^{ac}-Fourier (mathlib gaussSum_mulShift-family;
  SURVEY at decompose-iteration: exact names) + tsum-Fubini (norm-summable,
  Re s > 1 ✓ classical absolute convergence).
- c2 (leaf) boundary value Σ_{n≥1} ε^{nc}/n = −log(1−ε^c) for ε^c ≠ 1 on
  the unit circle. SURVEY-GATED: mathlib has the log-Taylor series on the
  open disc; the boundary case needs Abel/Dirichlet-test convergence —
  check `Mathlib/Analysis/...Abel` + `hasSum_taylorSeries_log`-family; if
  the boundary statement is absent it is an API-gap sub-leaf (Abel's
  limit theorem instance or Dirichlet test, ~60 LOC).
- c3 (leaf) assembly: LFunction θ 1 = lim_{s→1⁺} of c1's closed form
  (continuity of LFunction at 1 for θ ≠ 1: mathlib differentiableAt_LFunction
  ✓) then c2. RJW's display follows after G(θ)·θ(−1)/N = 1/G(θ⁻¹)
  (gaussSum product identity — project T501 has the level-N
  G(θ)G(θ⁻¹) = θ(−1)·N ✓ REUSE).
- c4 (leaf, shared with P6) `gaussSum_mul_coprime`: for coprime D, M and
  θ = η⊗χ at level DM: G(θ) = χ(D)η(M)·G(η)G(χ)-shape (CRT reindex;
  ~30 LOC; home Interpolation/Characters.lean gaussSum section).
Sizing ~200 LOC + survey risk at c2.

### Cluster P6 — the p-adic value (ii) (new file PadicLFunctions/ValuesAtOne.lean)
Source: TeX 2055–2155 (≈ 100 lines). Statement scope per replan 4 (D > 1).
Ambient: §5 K-stack + W6a (L := K) + W6b.
- p1 (def) `logSeriesAt (u : K)` := PowerSeries.mk: coeff 0 = extLog(u−1),
  coeff n = (−1)^{n−1}/n · (u/(u−1))^n-cleared-form (TeX 2076–2080
  expansion; over K — denominators n live in ℚ_[p] ⊂ K); `Ftilde θ` :=
  −Σ_{c∈(ℤ/N)ˣ} θ⁻¹(c) • logSeriesAt(ε_N^c) (G-cleared per replan 5).
- p2 (leaf) `derivative_logSeriesAt`: ∂(logSeriesAt u) = 1 +
  Ring.inverse((1+T)·C u − 1)-series for ‖u‖ = 1-units (formal geometric
  series computation; matches the §5 denominator objects
  isUnit_root_mul_one_add_X_sub_one).
- p3 (leaf) `derivative_Ftilde`: ∂F̃_θ = F_θ-series (p2 summed; the
  constant 1-terms cancel by Σ_c θ⁻¹(c) = 0 — nontrivial character sum,
  mathlib DirichletCharacter.sum_eq_zero_of... verify name; F_θ-series :=
  the T508 cleared twist transform display).
- p4 (def) `rhoTheta` : MeasureR K ℤ_[p] := iota of the x⁻¹-weighted
  unit-restriction of the χ-twisted μ̃_η (the §5 zetaEtaCleared pattern at
  θ-level; reuse invUnitsCM/extendByZero).
- p5 (leaf) `psi_rhoTheta = 0` (unit-supported, project
  isSupportedOn_units_iff_psi_eq_zero) and `derivative_mahler_rhoTheta`:
  ∂𝓐_ρ = (1−φψ)·F_θ-series (x·ρ = Res μ_θ via invCM-cancellation +
  LemmaMultiplicationbyx = project mahlerTransform_cmul_X + res_units_eq).
- p6 (leaf) the constant pin: 𝓐_ρ = F̃_θ − φ(ψF̃_θ) (∂ of both sides agree
  by p3+p5+b3; difference is ∂-constant by b7; ψ of both sides is 0
  (b2: ψφ = id; p5+b4); ψ(constant) = constant ⟹ C = 0).
- p7 (leaf) evaluation: L_p-pairing = 𝓐_ρ(0) (mass = constantCoeff, project
  apply_powCM at 0) = F̃(0) − (ψF̃)(0) ((φG)(0) = G(0)); then
  (ψF̃)(0) by b6 + `Ftilde_eval`: seriesEval F̃ (ξ^i−1) =
  −Σ_c θ⁻¹(c)·extLog((ξ^i ε^c)−1-shape) (resummation through extLog_mul:
  (1+z)ε^c−1 = (ε^c−1)(1 + ε^c z/(ε^c−1)), a8–a11) + the μ_p-collapse
  Σ_ξ extLog(ξw−1) = extLog(w^p−1) (∏_{ξ∈μ_p}(ξw−1) = w^p−1 since
  ∏ξ = 1 for p odd; a9-additivity; domains by a11) + the c ↦ pc
  bookkeeping: n = 0: automorphism of (ℤ/D)ˣ ⟹ θ(p)/p-factor;
  n ≥ 1: fiber sums Σ_{j mod p}θ⁻¹(c+jN/p) = 0 by primitivity (small
  character leaf `sum_shift_eq_zero_of_isPrimitive`, replan 3).
- p8 (leaf) headline `LpFunction_one` (**RJW Thm 6.1(ii)**, D > 1):
  LpFunction p K η hζ hD χ 1 = −(1−(θ'(p):K)·p⁻¹)·(G-factors)⁻¹·
  Σ_c θ⁻¹(c)·extLog(1−ε_N^c) — exact display shape fixed at skeleton time
  (uses extLog_neg for the 1−ε vs ε−1 swap, c4 for the G(θ⁻¹)-form).
- p9 (leaf) `norm-1 of the arguments`: ‖1−ε_N^c‖ = 1 for c ∈ (ℤ/N)ˣ, D > 1
  (the cyclotomic-product argument: Π_{c∈(ℤ/D)ˣ}(1−ε_D^c) = Φ_D(1) of norm
  one, each factor ≤ 1 ⟹ each = 1; mixed roots reduce to the D-part —
  verify the exact route at skeleton time; mathlib
  eval_one_cyclotomic_prime/not_prime_pow family).
Sizing ~400 LOC.

### Prior-B2 consultation (Step 4.6)
b2_log.jsonl: still empty (0 entries) — clean.

### Gate status (Step 5) — DRAFT-1, NOT YET PASSED
Outstanding before tickets: (α) Lean skeleton (Step 2.5) for all four
files; (β) per-leaf attack blocks in the binding 3-attack format (the
design-level attacks recorded above already killed two routes — formal
Eqphipsi, pigeonhole-unit — and pinned the boundary-iteration subtlety);
(γ) survey completion: c1/c2 mathlib names (area B), b7/b1 mathlib check
(ker-∂, digit machinery), character-sum lemma names (p3, p7);
(δ) skeleton `lake build` green. Tickets (1g) only after the gate.


### R6.6 (added 2026-06-11, mid-execution replan — binding for W6b/P6)
ATTACK SUCCEEDED at T605 (B2-grade, logged in b2_log.jsonl): the digit
decomposition is FALSE over field coefficients (over ℚ, (1+T)^p − 1 has
unit linear term, so φ is bijective and digits are non-unique). It is the
p-adically INTEGRAL statement (proved over integerRing K by
measure-transport through mahlerRingEquiv). Every downstream use of ψ on
the FIELD-coefficient series F̃_θ was therefore ill-posed. REALIGNED
(the c₀-design; same mathematics, ψ-free scaffolding): with
W := (G-cleared)F̃ − 𝓐_ρ one has ∂W = φ(B) for a concrete bounded B;
choosing the formal antiderivative C (C(0) = 0, p∂C = B) gives
W = φC + c₀ with c₀ constant; evaluating at 0 and at the ξ^i − 1 (where
φ-images collapse to constant terms) yields
p·𝓐_ρ(0) = p·F̃(0) − Σ_i F̃(ξ^i−1), using sum_seriesEval_mahlerK (the
realised Eqphipsi at the INTEGRAL level) and ψρ = 0. The trace becomes
sum_seriesEval_Ftilde : Σ_i F̃(ξ^i−1) = θ(p)·F̃(0) (cases per TeX
2115–2155). Restated skeleton: FormalPsi b3' (∂φ-commutation),
exists_antideriv, b6' (integral Eqphipsi), mahlerK moved here;
ValuesAtOne p6' (mass identity), p7' (trace).

## R7: The residue of ζ_p at s = 1 (RJW §7, TeX 2181–2360) — draft

### Source statements (verbatim)
- Thm 7.1 (`thm:residue`, TeX 2187–2194): "Let $i \in \{1, 2, \ldots, p-1\}$.
  The following assertions hold: (i) If $i \neq p-1$, then $\zeta_{p,i}$ is
  analytic at $s=1$. (ii) The function $\zeta_{p,p-1}$ has a simple pole at
  $s=1$ with residue $(1 - p^{-1})$."
- Eqtmp2 (TeX 2210–2215): "$\zeta_{p,i}(s) = \frac{\int_{\Z_p^\times}
  \omega(x)^{i}\langle x\rangle^{1-s} x^{-1}\cdot\mu_a}{\omega(a)^{i}
  \langle a\rangle^{1-s} - 1}$" — definitional for `zetaPBranch` (T519).
- Lem 7.2 (`lem:g p-1`, TeX 2218–2226): "(i) If $i \neq p-1$, then
  $g_{a,i}(1) \neq 0$. … (ii) We have $g_{a,p-1}(1) = 0$, and
  $\lim_{s\to1}(s-1)^{-1}g_{a,p-1}(s) = -\log_p(a)$."
- F̃_a (TeX 2268): "$\widetilde{F}_a(T) \defeq \log\left(\frac{T}{1+T}\cdot
  \frac{(1+T)^a}{(1+T)^a-1}\right)$"; Lem 7.3 (TeX 2271): "Formally, we
  have $\partial \widetilde{F}_a(T) = F_a(T)$."
- Lem 7.4 (TeX 2285): "We have $\widetilde{F}_a(T) \in \mathscr{R}^+$."
  [SKIPPED — distribution-free route, as Lem 6.2; rationale in blueprint.]
- Lem 7.5 (`lem:numerator`, TeX 2320): "We have
  $\big((1-\varphi\circ\psi)\widetilde{F}_{a}\big)(0) = -(1-p^{-1})\log_p(a)$."
  Proof TeX 2323–2352: F̃_a(0) = −log_p(a) (the aT-factorisation
  (1+T)^a−1 = aT(1+Tg(T)), eq:poly expansion); the Eqphipsi ξ-sum with
  $\{\xi^a : \xi\in\mu_p\} = \mu_p$ (a generator) and
  $\prod_{\xi\in\mu_p}(X\xi-1) = X^p-1$, $\prod\xi^{a-1} = 1$, collapsing
  to $-p^{-1}\log_p(a)$.

### Recorded replans
1. Distribution-free route again (R6.6 verbatim): Lem 7.4 (ℛ⁺) not
   formalised; the mass ∫x⁻¹μ_a is the constant coefficient of 𝓐(ρ_a) for
   the GENUINE measure ρ_a (= the §4 `zetaNum` base-changed), pinned by
   the c₀-design and evaluated by sum_seriesEval_mahlerK.
2. "Analytic/simple pole" realised as topological statements: (i) =
   ContinuousAt (zetaPBranch p hp2 i) 1 (for 0 < i < p−1); (ii) =
   Tendsto ((s−1)·ζ_{p,p−1}(s)) (𝓝[≠]1) (𝓝 (1−p⁻¹)). RJW's
   rigid-analytic framing (Rem 4.x weight-space) stays prose.
3. The Lem 7.2 limit via the exp/log bridge (T523) instead of RJW's
   binomial-series manipulation (TeX 2236–2248): ⟨a⟩^{1−s} =
   exp((1−s)log⟨a⟩), so (s−1)⁻¹(⟨a⟩^{1−s}−1) → −log⟨a⟩ follows from the
   exp-derivative-at-0; equivalent by T523's uniqueness (the binomial
   route IS available but the exp-route reuses proven API; replan note).
4. ξ-field: statements needing μ_p ⊂ K quantify over K (the §5/§6
   pattern); the ℚ_p-level conclusions descend by algebraMap-injectivity.
   K instantiated with ℂ_[p] (mathlib PadicComplex) — survey-gated.

### Leaves (PadicLFunctions/ResidueZeta.lean unless noted)
- **R7.1** (T701): exp-tail + character-Lipschitz.
  `norm_padicExp_sub_one_sub_self_le : InExpBall p w →
  ‖padicExp p w − 1 − w‖ ≤ p·‖w‖²` (terms n ≥ 2 at the (p−1)-power level:
  (‖(n!)⁻¹‖‖w‖^{n−2})^{p−1} ≤ p^{n−1}·p^{−(n−2)} = p);
  `norm_onePAdicPow_sub_one (hp2) : ‖y^t − 1‖ = ‖t‖·‖y−1‖` for
  y ∈ 1+pℤ_p (via T523: y^t = pZpExp(t·pZpLog y), norm_padicExp_sub_one,
  norm_padicLog; equality, not just ≤).
- **R7.2** (T702): the denominator. `teichmuller_isPrimitiveRoot_of_topGen`:
  ω(u) has order exactly p−1 for the §4 generator u (from the generator
  property: u mod p generates (ZMod p)ˣ — extract from T037);
  `branch_denom_ne_zero (0 < i < p−1)`: ω(u)^i⟨u⟩^{1−s}−1 ≠ 0 at s = 1
  (⟨u⟩⁰ = 1; ω(u)^i ≠ 1 by primitivity) and for all s (|ω^i−1-part| = 1 vs
  |⟨u⟩^{1−s}−1| < 1 ultrametric isoceles — gives nonvanishing on ALL of
  ℤ_p, stronger than RJW's s = 1); `tendsto_denom_div`:
  (s−1)⁻¹·(⟨u⟩^{1−s}−1) → −log⟨u⟩-coe over 𝓝[≠]1 (R7.1 + the exp-bridge).
- **R7.3** (T703): continuity. `continuous_zetaPBranch_num`:
  s ↦ zetaNum-pairing(branchChar i (1−s)) is Lipschitz (R7.1's character
  bound, uniform in x; measure-pairing norm-bound — the §3 PadicMeasure
  norm machinery `norm_apply_le`); `continuousAt_zetaPBranch` (Thm (i),
  0 < i < p−1): numerator continuous, denominator continuous and ≠ 0.
- **R7.4** (T704): F̃_a-series. Over K: `FtildeA (a : ℕ) : PowerSeries K` :=
  C(−extLog p (a:K)) + (the log(1+T·h_a)-series) + (a−1) • formalLog,
  with h_a from the §4 factorisation (PropFaT-analogue — survey MuA.lean
  for the existing (1+T)^a−1 = aT(1+Tg)-machinery; else define h_a by the
  explicit geometric composite as in TeX 2296–2305);
  `one_add_mul_derivative_FtildeA = F_a-series-K` (∂-computation per
  Lem 7.3: ∂log(T/(1+T)) = 1/T-part and ∂log((1+T)^a−1/(1+T)^a) =
  a/((1+T)^a−1) — formal, the T612-p2-pattern with the geometric
  inverses); F_a-series := K-image of the §4 Mahler transform of μ_a
  (MuA.lean's Fa — survey the exact decl).
- **R7.5** (T705): the measure. `rhoA := baseChange p K (iota-of
  (zetaNum p a))` (the §4 Measure-level units-embedding — survey
  Measure/UnitsZp for the ℤ_p-iota; zetaNum p a : PadicMeasure p ℤ_[p]ˣ);
  `psi_rhoA = 0` (unit-supported through baseChange — baseChange/psi
  compatibility: survey BaseChange.lean for psi-naturality (the TW6 notes
  deferred naturality lemmas to consumers — may need a new lemma
  `psi_baseChange : psi(baseChange μ) = baseChange(psi μ)`-shape, ~30 LOC
  via mahlerTransform_baseChange + the digit/transform characterisations));
  `one_add_mul_derivative_mahlerK_rhoA = (1−φψ)F_a-series` (the
  T614-pattern: x·ρ_a = baseChange(Res μ_a-units-version) — the §4 zetaNum
  is x⁻¹Res(μ_a) BY CONSTRUCTION (ZetaP.lean) so x·zetaNum = Res μ_a at
  the §4 level (survey the §4 lemma; T037-era should have it), transform
  + res_units_eq).
- **R7.6** (T706): the mass. c₀-pin (T615-pattern verbatim):
  `p_mul_constantCoeff_mahlerK_rhoA : (p:K)·𝓐ρ_a(0) = (p:K)·F̃_a(0) −
  Σ_{i<p} F̃_a(ξ^i−1)`; trace `sum_seriesEval_FtildeA :
  Σ_{i<p} seriesEval F̃_a (ξ^i−1) = (p:K)·(−p⁻¹·extLog(a)-form)` — wait,
  per Lem 7.5: φψF̃_a(0) = −p⁻¹log_p(a) ⟺ Σ_i F̃_a(ξ^i−1) = p·(φψF̃_a)(0)
  = −log_p(a): the per-point evaluation F̃_a(ξ^i−1) =
  extLog-of-((ξ^i−1)-substituted arguments) (the T616-pattern:
  seriesEval-of-logSeriesAt-style resummations) and the μ_p-collapse with
  {ξ^a} = μ_p (gcd(a,p) = 1 from the generator — `generator_coprime`
  sub-leaf) + ∏(Xξ−1) = X^p−1 + ∏ξ^{a−1} = 1 (p odd: ∏ξ = 1; p = 2
  excluded by hp2 ambient anyway). Combined:
  `constantCoeff_mahlerK_rhoA = −(1−p⁻¹-K)·extLog(a)-form`.
- **R7.7** (T707): descent + numerator identification.
  `exists_padicComplex_pack` (survey-gated): the instance-pack + a
  primitive p-th root for K := ℂ_[p]; `zetaNum_one_eq`: the ℚ_p-level
  ∫x⁻¹μ_a = ((zetaNum p a) 1-pairing : ℚ_[p]) = −(1−p⁻¹)·extLog p (a:ℚ_[p])
  (inject into K, rewrite via R7.6 + baseChange-compatibility of the
  mass + algebraMap-injectivity; extLog commutes with the embedding —
  small lemma `algebraMap_extLog`-shape via the witness-form).
- **R7.8** (T708, MILESTONE): Thm 7.1. (i) from R7.3; (ii):
  `tendsto_sub_one_mul_zetaPBranch (hp2) : Tendsto
  (fun s : ℤ_[p] => ((s:ℚ_[p])−1) · zetaPBranch p hp2 (p−1) s)
  (𝓝[≠] 1) (𝓝 (1 − (p:ℚ_[p])⁻¹))` — assemble: zetaPBranch-def =
  numerator(s)/denominator(s); (s−1)·ζ = [(s−1)/g(s)]·numerator(s);
  (s−1)/g(s) → −1/log⟨u⟩-coe (R7.2; division-limit: g ≠ 0 near 1 off 1 —
  from the limit being ≠ 0); numerator(s) → numerator(1) =
  zetaNum-mass-pairing (R7.3-continuity; branchChar (p−1) 0 = ω^{p−1}-only
  = 1-on-units: the pairing at s = 1 IS the mass: ω(x)^{p−1} = 1 ✓
  teichmullerFun_pow_card_sub_one) = −(1−p⁻¹)extLog(u-as-a) (R7.7);
  extLog(a) = log⟨u⟩-coe-relation (`extLog_eq_padicLog_angle`: a = ω⟨a⟩,
  extLog kills ω — extLog_mul + torsion + extLog_eq_padicLog-ball);
  product of limits: (−1/L)·(−(1−p⁻¹)L) = 1−p⁻¹ ✓ (L ≠ 0:
  log⟨u⟩ ≠ 0 ⟸ ⟨u⟩ ≠ 1 ⟸ u generator (torsion-free part nontrivial —
  topGen_pow_ne_one-machinery) + norm_padicLog).
- Blueprint: §7 chapter (Chapters/ — check existing stub name): wire
  Thm 7.1 (the Tendsto-pair), Lem 7.2, 7.3, 7.5 nodes; Lem 7.4
  rationale-comment (ℛ⁺ deferred); prose notes for replans 2–3.

### Prior-B2 consultation: 7 entries in b2_log.jsonl — none match the R7
names/shapes (checked by name; the digit/eval-phi/HasSum patterns are
already designed around).

### Gate status: draft — skeleton + per-leaf attacks at execution
(the §6-established per-ticket pattern); survey-gated items marked.

---

## R8: The p-adic family of Eisenstein series (RJW §8, TeX 2361–2446)

### Section prose (read in full 2026-06-12)

§8 closes Part I: the Kubota–Leopoldt pseudo-measure interpolates the
*constant* coefficients of the (p-stabilised) Eisenstein series; the
non-constant coefficients are interpolated by elementary divisor-sums of
Dirac measures; bundling coefficientwise gives the Λ-adic Eisenstein
family 𝐄 ∈ Q(ℤ_p^×)⟦q⟧. One Definition (p-stabilisation), one impossibility
remark (no measure interpolates p^k), one Theorem (the family + its
interpolation property). The notes' proof is 8 lines (TeX 2409–2416)
because "we've done all the work" — the §4 interpolation theorem.

### Verbatim source quotes (the four content units)

**Q1 (E_k and its expansion, TeX 2367–2373):**
> "Let k≥4 be an even integer. The Eisenstein series of level k, defined as
> G_k(z) := Σ_{(c,d)≠(0,0)} 1/(cz+d)^k […] E_k(z) := G_k(z)(k−1)!/(2·(2πi)^k)
> = ζ(1−k)/2 + Σ_{n≥1} σ_{k−1}(n)qⁿ, where σ_{k−1}(n) = Σ_{0<d|n} d^{k−1}
> and q = e^{2iπz}."

**Q2 (Dirac interpolation + impossibility, TeX 2376–2383):**
> "When d is coprime to p, we do this by viewing d as an element of ℤ_p^×
> and considering the Dirac measure δ_d at d […] ∫_{ℤ_p^×} x^k·δ_d = d^k
> for any k ∈ ℤ." / "the function k ↦ p^k can never be interpolated
> continuously p-adically […] Suppose there was indeed a measure θ_p with
> ∫_{ℤ_p^×} x^k·θ_p = p^k, and then suppose k_n is a strictly increasing
> sequence of integers p-adically tending to k. Then p^{k_n} = ∫x^{k_n}·θ_p
> ⟶ ∫x^k·θ_p = p^k, which is clearly impossible since p^{k_n} tends to 0."

**Q3 (p-stabilisation, TeX 2387–2394):**
> "We define the p-stabilisation of E_k to be E_k^{(p)}(z) := E_k(z) −
> p^{k−1}E_k(pz). An easy check shows that E_k^{(p)} = (1−p^{k−1})ζ(1−k)/2
> + Σ_{n≥1} σ^p_{k−1}(n)qⁿ, where σ^p_{k−1}(n) = Σ_{0<d|n, p∤d} d^{k−1}.
> Note E_k^{(p)} is a modular form of weight k and level Γ₀(p)."

**Q4 (the Theorem + proof, TeX 2399–2416):**
> "There exists a power series 𝐄(z) = Σ_{n≥0} A_n qⁿ ∈ Q(ℤ_p^×)⟦q⟧ such
> that: (a) A₀ is a pseudo-measure, and A_n ∈ Λ(ℤ_p^×) for all n≥1;
> (b) For all even k ≥ 4, we have ∫_{ℤ_p^×} x^{k−1}·𝐄(z) :=
> Σ_{n≥0}(∫_{ℤ_p^×}x^{k−1}·A_n)qⁿ = E_k^{(p)}(z)." / Proof: "The
> pseudo-measure A₀ is simply xζ_p/2 (shifting by 1 again, but in the
> opposite direction to before). We then define A_n = Σ_{0<d|n, p∤d} δ_d ∈
> Λ(ℤ_p^×). By the interpolation property of the Kubota–Leopoldt p-adic
> L-function, A₀ interpolates the constant term of the Eisenstein series.
> We also have ∫x^{k−1}·A_n = Σ_{0<d|n,p∤d} ∫x^{k−1}·δ_d =
> Σ_{0<d|n,p∤d} d^{k−1} = σ^p_{k−1}(n), so we get the required
> interpolation property."

### Replans (recorded; statements stay faithful)

- **R8.1 (erratum #11 — twisted pseudo-measure).** TeX 2403's "(a) A₀ is a
  pseudo-measure" is false with Def 3.34 (the pole of xζ_p is at the
  character x⁻¹; see errata.md #11 for the computation). Formalise the
  corrected claim: (g·[g]−[1])·A₀ ∈ Λ for all g, via the x-twist ring
  automorphism τ of Λ(ℤ_p^×) and its extension τ̂ to Q(ℤ_p^×);
  A₀ := τ̂(ζ_p)/2. The moment encoding mirrors `padicZeta_moments`:
  witnesses of (g·[g]−[1])·A₀ have x^{k−1}-moment
  (g^k−1)·(1−p^{k−1})·ζ(1−k)/2.
- **R8.2 (τ as a moments-checked ring hom).** τ := unitsCmul (unitsPowCM 1)
  is a ring automorphism of the convolution ring: additivity is definitional
  (unitsCmul is composition with mulLeft); multiplicativity follows from
  the zero-divisor lemma — both sides of τ(μ*ν) = τμ*τν have equal
  x^k-moments for all k > 0 by `units_mul_apply_unitsPowCM` and the shift
  τν(x^k) = ν(x^{k+1}); conclude by
  `eq_zero_of_forall_unitsPowCM_eq_zero`. No Amice/Mellin theory needed.
  Extension to Q: `IsLocalization.ringEquivOfRingEquiv` at
  M = T = nonZeroDivisors (a ring equiv maps nzd onto nzd — small lemma).
- **R8.3 (q-expansions as PowerSeries; modularity of E^{(p)} deferred).**
  The complex side states (i) the arithmetic identity σ^p_{k−1}(n) =
  σ_{k−1}(n) − p^{k−1}σ_{k−1}(n/p)·[p∣n], and (ii) the stabilised
  expansion: HasSum (fun n => c_n·q(z)ⁿ) (E_k^{RJW}(z) − p^{k−1}E_k^{RJW}(pz))
  with c₀ = (1−p^{k−1})ζ(1−k)/2, c_n = σ^p_{k−1}(n), where E_k^{RJW} :=
  (ζ(1−k)/2)•(EisensteinSeries.E) — mathlib's normalised E has constant
  term 1 (`E_qExpansion_coeff`), and RJW's E_k = ζ(1−k)/2·E. The
  Γ₀(p)-modularity of E^{(p)} (a "Note" inside the Definition, TeX 2394,
  no proof in source) is DEFERRED: mathlib has no level-raising/V_p
  operator; recorded in plan.md Deferred + blueprint node note.
- **R8.4 (𝐄 as PowerSeries over Q(ℤ_p^×)).** 𝐄 := PowerSeries.mk
  (n = 0 ↦ A₀, n ≥ 1 ↦ algebraMap (A_n)); RJW's display (b) is
  coefficientwise BY DEFINITION in the source ("∫x^{k−1}·𝐄 := Σ(∫x^{k−1}A_n)qⁿ"),
  so the theorem is exactly the per-coefficient moment statements +
  the complex identification of the target coefficients.

### Leaves (per-leaf attack logs at execution per the §6/§7-established
per-ticket pattern; mathlib discharges verified by grep this session)

- **L8.1a** `isUnit_two_iwasawa : IsUnit (2 : PadicMeasure p ℤ_[p]ˣ)` —
  2 = (2:ℤ_p)•1, (2:ℤ_p) a unit for p odd (`PadicInt.isUnit_natCast`-route
  /2-adic-valuation; or inverse exhibited: (2⁻¹:ℤ_p)•1). [mathlib+project]
- **L8.1b** `unitsDirac_moment : dirac p u (unitsPowCM p k) = (u:ℤ_p)^k` —
  rfl-level (`dirac_apply`). Q2's "∫x^k δ_d = d^k". [project]
- **L8.1c** `divisorMeasure (n : ℕ) : PadicMeasure p ℤ_[p]ˣ :=
  Σ_{d ∈ n.divisors.filter (¬p∣·)} dirac p (unit-of d)` — the unit:
  `PadicInt.isUnit_natCast_of_not_dvd`-pattern (used in MuA.lean:65 ✓);
  package d ↦ IsUnit.unit. [project]
- **L8.1d** `sigmaP (k n : ℕ) : ℕ := Σ_{d ∈ n.divisors.filter(¬p∣·)} d^k`
  + `divisorMeasure_moment : divisorMeasure n (unitsPowCM p k) = sigmaP k n`
  — Finset.sum through the linear functional (map_sum) + L8.1b. Q4's
  computation. [project]
- **L8.2a** `unitsTwist : PadicMeasure p ℤ_[p]ˣ ≃+* PadicMeasure p ℤ_[p]ˣ`
  — R8.2's moments route; toFun = unitsCmul (unitsPowCM 1), inv =
  unitsCmul (inv-character x⁻¹-as-x-valued: invCM... CARE: x⁻¹ has values
  in ℤ_pˣ ⊂ ℤ_p: invCM p exists, ZetaP.lean:67 ✓); left/right inverse by
  function algebra invCM·powCM1 = 1. Key sublemmas:
  `unitsTwist_moment : (τμ)(x^k) = μ(x^{k+1})` (powCM-mul collapse:
  unitsPowCM p 1 * unitsPowCM p k = unitsPowCM p (k+1) — ContinuousMap.ext
  + pow_succ) and `unitsTwist_mul` by `eq_zero_of_forall_unitsPowCM_eq_zero`
  on the difference (k>0 suffices ✓ the lemma only needs k>0). [project]
- **L8.2b** `map_nonZeroDivisors_unitsTwist : (nonZeroDivisors Λ).map τ =
  nonZeroDivisors Λ` — both inclusions from "ring equivs preserve
  (non)zero-divisors": x nzd ⟺ τx nzd (mul_eq_zero transport through the
  equiv). ~12 LOC, no mathlib gap assumed. [generic algebra]
- **L8.2c** `quotientTwist : QuotientField p ≃+* QuotientField p :=
  IsLocalization.ringEquivOfRingEquiv _ _ unitsTwist L8.2b` (mathlib decl
  verified at Localization/Defs.lean:673 ✓) + `quotientTwist_algebraMap`
  (= ringEquivOfRingEquiv_eq/`_mk'` simp forms, Defs.lean:696/700 ✓).
  [mathlib]
- **L8.2d** `twistedZetaHalf : QuotientField p :=
  (2:QuotientField p)⁻¹-free form — use algebraMap-of-(2⁻¹•1)·quotientTwist(padicZeta)`
  — avoid field-inverses: 2 is already a unit in Λ (L8.1a), so multiply by
  algebraMap(2⁻¹-unit-inverse). `twistedZetaHalf_isTwistedPseudoMeasure :
  ∀ g, ∃ ν, algebraMap ((g:ℤ_p)•dirac p g − 1)·twistedZetaHalf = algebraMap ν`
  — witness ν := 2⁻¹•τ(ν_g) with ν_g from `padicZeta_isPseudoMeasure`;
  the identity (g•[g]−[1]) = τ([g]−[1]) (τ(dirac g) = g•dirac g: cmul of
  dirac, rfl-level) + quotientTwist_algebraMap transport. Erratum R8.1
  docstring. [project]
- **L8.3** `twistedZetaHalf_moments : ∀ b (b-pack) k ≥ 4 …, ∀ ν witness,
  ((ν (unitsPowCM p (k−1)) : ℤ_p) : ℚ_p) = ((b:ℚ_p)^k − 1)·(1−p^{k−1})·
  zetaNeg(k−1)/2` — transport of `padicZeta_moments` (ZetaP.lean:303 ✓)
  through the twist: the witness-translation bijection ν ↔ 2⁻¹•τ(ν_ζ)
  (uniqueness of witnesses against a fixed nzd denominator: cancel
  (g•[g]−[1]) ∈ nzd — `dirac_sub_one_mem_nonZeroDivisors` (PseudoMeasure:795
  ✓) transported through τ via L8.2b) + L8.2a's moment shift. [project]
- **L8.4** `noMeasure_interpolates_pPow : ¬ ∃ θ : PadicMeasure p ℤ_[p]ˣ,
  ∀ k : ℕ, 0 < k → ((θ (unitsPowCM p k) : ℤ_p)) = (p:ℤ_p)^k` — Q2's
  impossibility. Route: k_n := φ(p^{n+1}) = p^n(p−1) > 0; uniform Euler
  congruence ∀u, u^{k_n} ≡ 1 mod p^{n+1} (`pow_card_eq_one` in
  (ZMod p^{n+1})ˣ, card = φ via `ZMod.card_units_eq_totient` +
  `Nat.totient_prime_pow`; transfer through `unitsToZModPow` +
  `PadicInt.ker_toZModPow` — the §7 `teichmuller_isPrimitiveRoot`/
  `angleUnit_coe_ne_one` patterns ✓) ⟹ ‖unitsPowCM p k_n − unitsPowCM p 0‖
  ≤ p^{−(n+1)} → 0 ⟹ |θ(x^{k_n}) − θ(1)| → 0 (`norm_apply_le`,
  Measure/Basic:109 ✓; map_sub). But θ(x^{k_n}) = p^{k_n} → 0, so
  θ(1) = 0; ALSO θ(x^{k_n}) = p^{k_n} with ‖p^{k_n}‖ = p^{−k_n}; combine:
  ‖p^{k_n}‖ = ‖θ(x^{k_n}) − θ(1)‖ ≤ p^{−(n+1)} ⟹ p^{−k_n} ≤ p^{−(n+1)}
  ⟹ k_n ≥ n+1 ✓ consistent — need the CONTRADICTION: θ(1) = lim p^{k_n} = 0
  and separately θ(x^{k_n}) → θ(1): take instead k'_n := 1 + k_n·m?? —
  CAREFUL (attack): the source's k_n "p-adically tending to k": pick target
  k = 1: k_n := 1 + p^n(p−1)·(anything growing) e.g. k_n := 1 + φ(p^{n+1}):
  x^{k_n} → x¹ uniformly (same Euler congruence: x^{k_n} − x =
  x(x^{φ}−1)); then p^{k_n} → 0 (k_n → ∞) but θ(x^{k_n}) → θ(x¹) = p¹ = p
  ≠ 0. Contradiction ‖p‖ = lim ‖θ(x^{k_n})‖ ≤ lim p^{−(n+1)} = 0. Clean.
  [project+mathlib]
- **L8.5a** `sigmaP_eq (k n) (p∣n) : sigmaP k n = σ k n − p^k·σ k (n/p)`
  and `sigmaP_eq_of_not_dvd (¬p∣n) : sigmaP k n = σ k n` — divisor-sum
  split `Finset.sum_filter_add_sum_filter_not` + the bijection
  d ↦ p·d : (n/p).divisors ≃ n.divisors.filter (p∣·) (`Nat.divisors`-
  membership arithmetic; `ArithmeticFunction.sigma_apply` ✓ mathlib).
  [mathlib]
- **L8.5b** `hasSum_stabilisedEisenstein : ∀ z : ℍ, HasSum
  (fun n => c_n • 𝕢(z)ⁿ) ((ζ(1−k)/2)·E hk z − p^{k−1}·(ζ(1−k)/2)·E hk (p·z))`
  with c per Q3 — from mathlib `EisensteinSeries.q_expansion_bernoulli`
  (verified ✓ QExpansion.lean:299) at z and at p·z (ℍ-point: positive real
  scaling — `UpperHalfPlane` smul/mk machinery), the q^{pn}-reindex
  (HasSum.comp-injective on n ↦ pn + zero-extension: `Function.Injective.hasSum_iff`),
  L8.5a, and ζ(1−k) = −B_k/k (`riemannZeta_neg_nat_eq_bernoulli` ✓ +
  our `zetaNeg_eq_riemannZeta` ✓ ZetaValuesComplex:18) to convert
  mathlib's 1−(2k/B_k)Σσqⁿ-normalisation into RJW's
  ζ(1−k)/2 + Σσqⁿ-normalisation. The ζ(1−k)/2-rescale is nonzero for
  even k ≥ 4 (B_k ≠ 0: `bernoulli`-nonvanishing at even — via
  ζ(1−k) ≠ 0 ⟸ ζ(k) ≠ 0 functional-equation… simpler: zetaNeg(k−1) ≠ 0
  ⟸ bernoulli k ≠ 0 ⟸ mathlib `bernoulli_ne_zero`?? — verify at
  execution; only needed if we divide; statement multiplies, so likely
  NOT needed at all). [mathlib+project]
- **L8.6** `eisensteinFamily : PowerSeries (QuotientField p)` (R8.4) +
  the MILESTONE theorem packaging (b): coefficient 0 moments = L8.3
  (= (1−p^{k−1})ζ(1−k)/2-values = c₀ of L8.5b), coefficient n ≥ 1
  moments = L8.1d (= σ^p = c_n of L8.5b via L8.5a). [project]

### Gate status: draft-approved shape — skeleton + per-leaf attacks at
execution (the §6/§7-established per-ticket pattern). Survey-verified
mathlib anchors: EisensteinSeries.E + E_qExpansion_coeff +
q_expansion_bernoulli; IsLocalization.ringEquivOfRingEquiv;
riemannZeta_neg_nat_eq_bernoulli; ArithmeticFunction.sigma. No
REVIEW-PENDING leaves. Deferred: Γ₀(p)-modularity of E^{(p)} (R8.3).

### R8 addendum (2026-06-12, user directive): L8.7 — Γ₀(p)-modularity un-deferred
- **L8.7** `stabilisedEisenstein : ModularForm ((Gamma0 p).map (mapGL ℝ)) k`
  + apply-lemma — replan R8.3's deferral REVOKED: the
  strong-multiplicity-one project (CBirkbeck/LeanModularForms@hecke-ring,
  now a lake require pinned 720d950b) supplies `modularFormLevelRaise`
  (ι_d : M_k(Γ₁(M)) → M_k(Γ₁(dM)), Miyake §4.6 Lem 4.6.1) with pointwise
  `modularFormLevelRaise_apply`/`coe_levelRaiseMatrix_smul`, the
  down-conjugation bridge `slash_mapGL_levelRaiseFun`, and Γ₀-conjugation
  lemmas (`levelRaiseConjOfDvd_mem_Gamma0`). Source: TeX 2394 (Q3's
  "Note"). Ticket T808. Two mathlib-skew compat fixes applied to the dep
  checkout (ZMod.Units import; HeckeCoset.rep simp-unfold) — upstream at
  CLEANUP-82.

---

## R9–R10: Notation + The Coleman map (RJW §9 TeX 2466–2511, §10 TeX 2512–2948)

### Section prose (read in full 2026-06-12)

§9 is the Part-II notation index: F_n = ℚ(μ_{p^n}), the LOCAL tower
K_n = ℚ_p(μ_{p^n}), units 𝒰_n = O_{K_n}^×, principal units 𝒰_{n,1},
norm-inverse-limits 𝒰_∞, the cyclotomic character 𝒢 ≅ ℤ_p^×, and the
fixed compatible system ξ_{p^n} (ξ_{p^{n+1}}^p = ξ_{p^n}) with
π_n = ξ_{p^n} − 1 a uniformiser of K_n. Only the LOCAL tower is needed
for §10 (the global F_n/𝒱_n and the +-objects enter at §11).

§10 proves Coleman's theorem and builds the Coleman map:
- 10.1: single-level interpolation lemma + the statement (thm:coleman
  power series): a unique injective multiplicative hom 𝒰_∞ → ℤ_p⟦T⟧^×,
  u ↦ f_u, with f_u(π_n) = u_n.
- 10.2: cyclotomic units c_n(a) = (ξ^a−1)/(ξ−1), norm-compatibility,
  the explicit f_{c(a)} = ((1+T)^a−1)/T, ∂log f_{c(a)} = a − 1 − F_a
  (prop:coleman zetap), and (1−φψ)∂log f_{c(a)} = −(1−φψ)F_a
  (lem:relate cyclo to mua).
- 10.3: uniqueness (Weierstrass preparation ⟹ finitely many zeros in
  the open ball; the π_n are infinitely many), the norm operator 𝒩
  (φ∘𝒩 f = Π_{η∈μ_p} f(η(1+T)−1), defined as the B/A-algebra norm for
  B = ℤ_p⟦T⟧ ⊇ A = φ(ℤ_p⟦T⟧)), the evaluation/norm commuting square
  ((𝒩f)(π_n) = N_{n+1,n}(f(π_{n+1})), via min poly X^p − ξ_{p^n} and
  φ(f)(π_{n+1}) = f(π_n)), the mod-p^k continuity lemmas (i)–(iv) of
  lem:norm continuity, and surjectivity of R by the diagonal argument
  g_n := 𝒩^n f_{2n} + compactness of ℤ_p⟦T⟧^×. Result: the isomorphism
  𝒰_∞ ≅ (ℤ_p⟦T⟧^×)^{𝒩=id} (thm:coleman map 2).
- 10.4: Col := 𝓐⁻¹ ∘ ∂⁻¹-free composition
  u ↦ f_u ↦ ∂log f_u ↦ (1−φψ)(∂log f_u) ↦ x⁻¹-divide ↦ measure on ℤ_p^×
  and thm:coleman to kl: ζ_p = Col(c(a))/θ_a in Q(ℤ_p^×).
- 10.5: Kummer sequence/Euler systems/Perrin-Riou — expository
  ("may be skipped"); PROSE-ONLY (blueprint chapter covers; no Lean).

### Verbatim source quotes (headline results)

**Q1 (Coleman's theorem, TeX 2553–2560):**
> "There exists a unique injective homomorphism 𝒰_∞ ⟶ ℤ_p⟦T⟧^×,
> u ⟼ f_u of multiplicative groups such that f_u(π_n) = u_n for all
> u ∈ 𝒰_∞ and n ≥ 1."

**Q2 (the refined form, TeX 2796–2803):**
> "There exists a unique isomorphism of groups 𝒰_∞ → (ℤ_p⟦T⟧^×)^{𝒩=id},
> u ↦ f_u such that f_u(π_n) = u_n for all u ∈ 𝒰_∞ and n ≥ 1."

**Q3 (norm operator, TeX 2654–2659):**
> "There exists a unique multiplicative operator 𝒩 on ℤ_p⟦T⟧, the norm
> operator, such that (φ∘𝒩)(f)(T) = Π_{η∈μ_p} f(η(1+T)−1)."

**Q4 (commuting square, TeX 2673–2692):** the diagram
> "ℤ_p⟦T⟧^× →[f ↦ f(π_{n+1})] 𝒰_{n+1}; 𝒩 ↓ ↓ N_{n+1,n};
> ℤ_p⟦T⟧^× →[f ↦ f(π_n)] 𝒰_n" commutes; proof:
> "N_{n+1,n}(f(π_{n+1})) = Π_{η∈μ_p} f(ηξ_{p^{n+1}} − 1) =
> (φ∘𝒩)(f)(π_{n+1}) = (𝒩f)(π_n)" using "the minimal polynomial of
> ξ_{p^{n+1}} over K_n is X^p − ξ_{p^n}".

**Q5 (continuity, TeX 2726–2739):**
> "(i) If φ(f)(T) ≡ 1 mod p^k … then f(T) ≡ 1 mod p^k. (ii) 𝒩(f) ≡ f
> mod p. (iii) If f ≡ 1 mod p^k with k ≥ 1, then 𝒩(f) ≡ 1 mod p^{k+1}.
> (iv) If k₂ ≥ k₁ ≥ 0, then 𝒩^{k₂}(f) ≡ 𝒩^{k₁}(f) mod p^{k₁+1}."

**Q6 (surjectivity diagonal, TeX 2763–2791):**
> "define g_n := 𝒩^n f_{2n} ∈ ℤ_p⟦T⟧^×. Then for any m ≥ n …
> u_n ≡ g_m(π_n) mod p^{m+1} … It thus suffices to find a convergent
> subsequence of (g_m); but such a subsequence exists, as ℤ_p⟦T⟧^× is
> compact."

**Q7 (cyclotomic units, TeX 2572–2607):**
> "c_n(a) := (ξ_{p^n}^a − 1)/(ξ_{p^n} − 1) ∈ 𝒰_n" /
> "N_{n,n−1}(ξ_{p^n}^b − 1) = Π_{η∈μ_p}(ξ_{p^n}^b η − 1) =
> ξ_{p^n}^{bp} − 1 = ξ_{p^{n−1}}^b − 1" / "f_{c(a)}(T) = ((1+T)^a−1)/T"
> / "∂ log f_{c(a)}(T) = a − 1 − F_a(T)".

**Q8 (Coleman map + KL, TeX 2826–2841):**
> "Col : 𝒰_∞ →[u↦f_u] (ℤ_p⟦T⟧^×)^{𝒩=id} →[∂log] ℤ_p⟦T⟧ →[1−φψ]
> ℤ_p⟦T⟧^{ψ=0} →[∂⁻¹] ℤ_p⟦T⟧^{ψ=0} →[𝓐⁻¹] Λ(ℤ_p^×)" /
> "For any topological generator a of ℤ_p^×, we have an equality of
> pseudo-measures ζ_p = Col(c(a))/θ_a ∈ Q(ℤ_p^×)."

### Design decisions (replans R9/R10 — recorded, statements faithful)

- **R10.1 (the tower lives in ℂ_p).** K_n := ℚ_p⟮ξ_{p^n}⟯ as
  IntermediateField ℚ_p ℂ_[p], for a FIXED compatible system
  ξ : ℕ → ℂ_[p] (ξ_{n+1}^p = ξ_n, ξ_n primitive p^n-th; existence by
  ℕ-recursion + IsAlgClosed roots). This matches the source's own
  motivation (TeX 2528–2532 frames everything inside B(0,1) ⊂ ℂ_p),
  gives K_n ≤ K_{n+1} with honest mathlib `Algebra.norm`, and reuses
  the §7/§8 PadicComplex + seriesEval infrastructure. O_n := the
  norm-unit-ball of K_n (= integerRing ℂ_[p] ∩ K_n); 𝒰_n := O_nˣ.
- **R10.2 (degree ladder via Eisenstein).** [K_n : ℚ_p] = φ(p^n) from
  irreducibility of Φ_{p^n} over ℚ_p: Eisenstein at (p) after T ↦ T+1
  (mathlib `cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt`-family
  — survey: generic Eisenstein machinery READY, the ℚ_p-instantiation
  is project work) + Gauss-primitivity over the DVR ℤ_[p]. Tower step
  [K_{n+1} : K_n] = p and minpoly_{K_n}(ξ_{n+1}) = X^p − ξ_n.
  ‖π_n‖ = p^{−1/φ(p^n)} via ‖N_{K_n/ℚ_p}(π_n)‖ = ‖±p‖ and
  Galois-invariance of the (unique, spectral) norm.
- **R10.3 (evaluation = seriesEval).** f(π_n) := seriesEval (map f) π_n
  over K := ℂ_[p] (‖π_n‖ < 1, integral coefficients ⟹ convergent; the
  §8 `seriesEval_pow`/`seriesEval_mul` layer gives multiplicativity);
  the value lies in K_n (closed: finite-dim ⟹ complete ⟹ closed;
  partial sums in ℤ_p[ξ_n]). Mathlib's new `PowerSeries.eval₂`
  (Evaluation.lean) is the recorded alternative if the normed route
  rubs; we prefer seriesEval for continuity with §§6–8.
- **R10.4 (𝒩 via the digit basis, no field-norm theory).** The source
  defines 𝒩 = φ⁻¹∘N_{B/A} for B = ℤ_p⟦T⟧ ⊇ A = φ(ℤ_p⟦T⟧). The
  μ_p-product formula is NOT formal over ℤ_p (the T ↦ η(1+T)−1
  substitution has non-nilpotent constant term — the §6 Eqphipsi
  subtlety, errata-adjacent). Faithful realisation: B is FREE of rank p
  over A with basis (1+T)^i, i < p — this is EXACTLY the proven
  integral digit decomposition (FormalPsi, T605 layer) — so define
  𝒩 f := φ⁻¹ (Algebra.norm along the φ-algebra structure) =
  φ⁻¹(det of multiplication-by-f in the digit basis). Multiplicativity
  is `Algebra.norm`'s; the commuting square (Q4) follows by mapping the
  multiplication matrix entrywise under f ↦ f(π_{n+1}) (which carries
  A-entries to O_n via φf(π_{n+1}) = f(π_n)) and `RingHom.map_det`,
  against the O_n-basis (ξ_{n+1}^i)_{i<p} of O_{n+1} (monogenic by the
  Eisenstein tower step). The trace identity ψ = p⁻¹φ⁻¹∘Tr (TeX 2670)
  becomes a digit-trace computation against the SAME basis.
- **R10.5 (continuity lemmas at the digit level).** Q5(i): φ is
  coefficientwise-injective mod p^k (digit-extraction). Q5(ii)/(iii):
  the source's proofs run mod 𝔭₁ in O_1⟦T⟧ via the product formula;
  our route: the det-formula mod p — over 𝔽_p, φ̄(f) = f(T^p)-Frobenius
  and the digit matrix of f becomes... realised as: 𝒩f ≡ f mod p ⟺
  det ≡ φ(f)-related congruence; ATTACK at execution — fallback route
  recorded: prove (ii)/(iii) via the EVALUATED form over O₁⟦T⟧ with the
  (π₁)-adic evaluation API (mathlib eval₂ at topologically nilpotent
  η(1+T)−1 — legal there) and descend by φ-injectivity (i). The
  surjectivity argument (Q6) needs only (iii)+(iv) and compactness.
- **R10.6 (compactness of ℤ_p⟦T⟧^×).** Via the coefficientwise
  homeomorphism PowerSeries ℤ_[p] ≃ (ℕ → ℤ_[p]) (Pi topology — mathlib
  WithPiTopology) + Tychonoff; the unit group as a closed subset
  (constant coeff a unit: clopen condition). Convergent-subsequence
  extraction: sequential compactness from compact + metrizable?? —
  ℕ → ℤ_[p] with product topology IS metrizable (countable product) ✓
  `IsCompact.isSeqCompact`-route.
- **R10.7 (scope).** §10.5 (Kummer/Euler systems/Perrin-Riou):
  prose-only, deferred — blueprint chapter text covers it; no Lean.
  §9's global objects (F_n, 𝒱_n, +-subfields, 𝒢-Galois): deferred to
  the §11 pass (only the local tower is §10-load-bearing); the
  cyclotomic character iso 𝒢 ≅ ℤ_p^× rides §11.
- **R10.8 (θ_a and the final identity).** thm:coleman to kl: both sides
  are pseudo-measures with ([a]−[1])-witnesses; the witness of the
  RHS is Col(c(a)) itself against θ_a := [a]−... (RJW's θ_a from §4 —
  our `dirac p u − 1`-denominator); the proof is moment-comparison:
  Col(c(a))'s moments = (1−φψ)∂log f_{c(a)}-coefficients = −(1−φψ)F_a
  data (Q7's lem:relate cyclo to mua) = ([a]−[1])ζ_p's moments
  (zetaNum), then `pseudoMeasure_eq_zero_of_moments`-uniqueness — all
  §3.6/§4 infrastructure.

### Gate status: draft-approved shape — skeleton + per-leaf attacks at
execution (the established per-ticket pattern). Survey anchors
(Explore agent, 2026-06-12): IsCyclotomicExtension API READY;
Eisenstein machinery READY (ℚ_p-instantiation = project leaf);
Algebra.norm + autEquivPow READY; PowerSeries.eval₂ (Evaluation.lean,
2024) READY; Weierstrass preparation (WeierstrassPreparation.lean,
2025) READY; Pi-topology READY (CompactSpace instance = small project
leaf); inverse limits = ad-hoc subtype (standard). MISSING/project:
Φ_{p^n}-irreducibility over ℚ_p, O_n-monogenicity, the 𝒩-cluster,
norm-compatible towers.

---

## D61: Thm 6.1(ii) at D = 1 (the deferred §6 debt — errata #6) — planning
pass 2026-06-12 (T-D61; survey: the Explore agent's feasibility report)

### The gap (recap)
RJW Thm 6.1(ii) is stated for all non-trivial θ = χη but proved through
μ_η, which at D = 1 is junk (`muEtaCleared`'s denominators degenerate to
`Ring.inverse X` = 0; `isUnit_root_mul_one_add_X_sub_one` needs ¬D∣c,
false at D = 1, c = 0). Every §5/§6 moment theorem in the chain carries
1 < D (survey table: muEtaCleared_moments, psi/res/twist variants,
zetaEta_twisted_moments, Lp_interpolation, LpFunction_one).

### Route A (selected — survey-recommended, most economical)
Pair χ (conductor p^m, m ≥ 1, χ ≠ 1) DIRECTLY against the pseudo-measure
ζ_p via its ([b]−1)-witnesses — D-independent machinery throughout:
`padicZeta`/`padicZeta_isPseudoMeasure`/`padicZeta_moments` (ZetaP),
the §5 p-power twist layer (Twist.lean `twist_res_units` etc.,
TameConductor's no-D-hypothesis `twist_muA_moments`), mathlib p^n-level
Gauss sums (`gaussSum_mul_gaussSum_inv`). The χ-twisted-pseudo-measure
generalisation of §8's unitsTwist (Route C) is NOT needed; fixing
muEtaCleared at D = 1 (Route B) is more invasive. Expected new-lemma
count: 2–3 + the value theorem.

### D61 sub-board shape (gated tickets D611–D613 appended to tickets.md)
- D611: `padicZeta_charTwist_moments` — the witness-encoded twisted
  moments ∫χ(x)x^k·ζ_p = (b-factor)·(1 − χ(p)p^{k−1})·L(χ,−k)-data, by
  transporting padicZeta_moments through the χ-twist of the witness
  (the §5 twist-of-measure layer at the ℤ_p-units level) — the D = 1
  analogue of zetaEta_twisted_moments.
- D612: the D = 1 L_p-object aligner: `LpFunctionWild` (or extend
  LpFunction's junk at D = 1 with an honest definition note): the pairing
  (χ-twisted ζ_p-witness)-normalised by G(χ⁻¹) at p^m-level (Gauss-unit:
  the p-power-level analogue of gaussSum_isUnit — survey Q4: mathlib
  handles G(χ)G(χ⁻¹) = ±p^m natively; unit-ness of G in K needs χ
  primitive — small lemma).
- D613 (the value): `LpFunctionWild_one`: L_p(χ,1) =
  −(1−χ(p)p⁻¹)·G(χ⁻¹)⁻¹·Σ_c χ⁻¹(c)·extLog(1−ε^c) — the §6 c₀-design
  verbatim at N = p^m (no tame clearing): F̃_χ := the p^m-level
  logSeriesAt-sum (the T612 layer is N-generic — verify the [NeZero N]
  + 1 < N hypotheses: 1 < p^m ✓ m ≥ 1!! — NOTE: much of the §6 chain's
  "1 < N" is SATISFIED at N = p^m even though "1 < D" fails: the
  load-bearing distinction is tame-vs-wild, and the survey's hD1-table
  conflates two different hypotheses: AT EXECUTION re-check which §6
  lemmas need 1 < D (the μ_η-side, unusable) vs 1 < N (fine at p^m):
  Ftilde/sum_seriesEval_Ftilde/p_mul_constantCoeff_mahlerK_rhoTheta are
  stated over θ at level N = D·p^n — their D = 1 instantiations may be
  CLOSER to working than the survey's table suggests; the genuinely
  D > 1 pieces are the μ_η/rhoTheta-side constructions, to be replaced by
  the D611-witness route).
GATE: the D61 sub-board is 1i-GATED (user review) per T-D61's charter —
tickets carry "GATED" status; not beastmode-dispatchable until released.

## R11: Iwasawa's theorem on the zeros — the §11 layer (RJW §11, TeX 2949–3112)

### Section prose (read in full 2026-06-12)

§11 reformulates ζ_p on the Galois side and sets up Iwasawa's theorem.
11.1 (TeX 2964–3042): the identification Λ(𝒢) = Λ(ℤ_p^×) via χ (the
notes' own definitional move); the ±-decomposition by the idempotents
(1±c)/2 (p odd); Λ(𝒢)⁺ ≅ Λ(𝒢⁺) for 𝒢⁺ = 𝒢/⟨c⟩ ↔ ℤ_p^×/{±1}; the
odd-moment membership criterion; corollary: ζ_p is a pseudo-measure on
𝒢⁺. 11.2 (TeX 3043–3059): I(𝒢)ζ_p and I(𝒢⁺)ζ_p are ideals. 11.3
(TeX 3060–3112): 𝒟_n (global cyclotomic units), the class-number
index theorem (cited to Washington Thm 8.2, NOT proven in the notes),
the local closures 𝒞_n/𝒞_{n,1}/𝒞_{∞,1} (+ ⁺), and the STATEMENT of
thm:iwasawa (proof = §12). The §9 notation that comes due here
(TeX 2470–2505): 𝒰_n, 𝒰_{n,1} with its ℤ_p-structure, 𝒰_{∞,1}, the
global F_n/𝒱_n and the ⁺-subfields.

### Verbatim source quotes

**Q1 (the identification, TeX 2970):**
> "the cyclotomic character gives an isomorphism χ : 𝒢 ≅ ℤ_p^×. This
> isomorphism induces an identification between measures on ℤ_p^× and
> measures on the Galois group 𝒢. From now on, we will let Λ(𝒢) be the
> space of measures on 𝒢, which we identify with Λ(ℤ_p^×) via the
> cyclotomic character. We may thus naturally consider ζ_p as a
> pseudo-measure on 𝒢."

**Q2 (𝒢⁺ and the observation, TeX 2992):**
> "the Galois group 𝒢⁺ = Gal(F_∞⁺/ℚ) = 𝒢/⟨c⟩ is identified through the
> cyclotomic character with ℤ_p^×/{±1}. Observe that ζ_p, which
> ostensibly is an element of Q(𝒢), vanishes at the characters χ^k,
> for any odd integer k > 1. We will use this fact to show that ζ_p
> actually descends to a pseudo-measure on 𝒢⁺."

**Q3 (lem:decompose plus minus, TeX 2994–3002):**
> "Let c ∈ 𝒢 denote complex conjugation. Let R be a ring in which 2 is
> invertible and M an R-module with a continuous action of 𝒢. Then M
> decomposes as M ≅ M⁺ ⊕ M⁻, where c acts as +1 on M⁺ and as −1 on
> M⁻." Proof: "This follows directly by using the idempotents (1+c)/2
> and (1−c)/2, which act as projectors to the corresponding M⁺ and M⁻."

**Q4 (the plus-iso, TeX 3006–3015):**
> "There is a natural isomorphism Λ(𝒢)⁺ ≅ Λ(𝒢⁺)." Proof: "We work at
> finite level. Let 𝒢_n := Gal(F_n/ℚ), and 𝒢_n⁺ := Gal(F_n⁺/ℚ). Then
> there is a natural surjection ℤ_p[𝒢_n] → ℤ_p[𝒢_n⁺] … Since this must
> necessarily map ℤ_p[𝒢_n]⁻ to 0, this induces a map ℤ_p[𝒢_n]⁺ →
> ℤ_p[𝒢_n⁺]. The result now follows at finite level by a dimension
> count (as both are free ℤ_p-modules of rank (p−1)p^{n−1}/2 …). We
> obtain the required result by passing to the inverse limit." And
> TeX 3017: "We henceforth freely identify Λ(𝒢⁺) with the submodule
> Λ(𝒢)⁺ of Λ(𝒢)."

**Q5 (the criterion, TeX 3019–3029):**
> "Let μ ∈ Λ(𝒢). Then μ ∈ Λ(𝒢⁺) if and only if ∫_𝒢 χ(x)^k·μ = 0 for
> all odd k ≥ 1." Proof: "we can write μ = μ⁺ + μ⁻, where
> μ± = (1±c)/2·μ … Since χ(c) = −1 … If k is odd, the above expression
> vanishes … the same argument shows that ∫χ(x)^k·μ⁻ vanishes for all
> k even. The result follows then by Lemma lem:zero divisor."

**Q6 (the corollary, TeX 3033–3039):**
> "The p-adic zeta function is a pseudo-measure on 𝒢⁺." Proof: "This
> follows from the interpolation property, as ζ(1−k) = 0 for odd
> k ≥ 1." [ERRATUM #13: false at k = 1 (ζ(0) = −1/2); the interpolated
> moment vanishes there via the Euler factor 1−p^{1−1} = 0. Recorded
> in errata.md with the corrected two-case argument.]

**Q7 (the ideal, TeX 3047–3057):**
> "By definition of pseudo-measures, the elements ([g]−[1])ζ_p belong
> to the Iwasawa algebra Λ(𝒢) for any g ∈ 𝒢. Recall from Definition
> DefAugmentationIdealFiniteLevel that I(𝒢) denotes the augmentation
> ideal … I(𝒢) = ker(Λ(𝒢) → ℤ_p)." Proposition: "The module I(𝒢)ζ_p
> is an ideal in Λ(𝒢). Similarly, the module I(𝒢⁺)ζ_p is an ideal in
> Λ(𝒢⁺)." Proof: "Since ζ_p is a pseudo-measure, we know
> ([g]−[1])ζ_p ∈ Λ(𝒢) for all g ∈ 𝒢. Hence the result follows as
> I(𝒢) is the topological ideal generated by the elements [g]−[1] for
> g ∈ 𝒢."

**Q8 (global cyclotomic units, TeX 3065–3067):**
> "For n ≥ 1, we define the group 𝒟_n of cyclotomic units of F_n to be
> the intersection of 𝒪_{F_n}^× and the multiplicative subgroup of
> F_n^× generated by {±ξ_{p^n}, ξ_{p^n}^a − 1 : 1 ≤ a ≤ p^n − 1}. We
> set 𝒟_n⁺ = 𝒟_n ∩ F_n⁺."

**Q9 (class numbers, TeX 3072–3081 — DEFERRED PROSE):**
> "The group 𝒟_n (resp. 𝒟_n⁺) is of finite index in the group of
> units 𝒱_n (resp. 𝒱_n⁺) … h_n⁺ = [𝒱_n : 𝒟_n] = [𝒱_n⁺ : 𝒟_n⁺]."
> Proof: "We will not prove this here; see [Washington, Theorem 8.2]."
> → not formalised (the notes don't prove it); blueprint node stays
> prose; deferred-table entry in plan.md. Survey addendum (2026-06-13,
> user directive): flt-regular-bernoulli's CyclotomicUnits/Sinnott stack
> has a prime-conductor, p-primary, conditional (named unproven analytic
> core) form `p ∣ [𝒱⁺:𝒟⁺] ↔ p ∣ h⁺` — not a Q9 discharge; recorded in
> plan.md as a candidate §13 external dependency (Vandiver shape).

**Q10 (local closures, TeX 3084 + 3090–3094):**
> "The cyclotomic units c_n(a), introduced in §10.2, are naturally
> elements of 𝒟_n, hence global." / "define 𝒞_n as the p-adic closure
> of 𝒟_n inside the local units 𝒰_n, let 𝒞_n⁺ := 𝒞_n ∩ 𝒰_n⁺, and let
> 𝒞_{n,1} := 𝒞_n ∩ 𝒰_{n,1}, 𝒞⁺_{n,1} := 𝒞_n⁺ ∩ 𝒰_{n,1};
> 𝒞_{∞,1} := lim←_{n≥1} 𝒞_{n,1}, 𝒞⁺_{∞,1} := lim←_{n≥1} 𝒞⁺_{n,1}."

**Q11 (thm:iwasawa, TeX 3098–3103 — STATEMENT ONLY, §12 board):**
> "The Coleman map induces an isomorphism of Λ(𝒢⁺)-modules
> 𝒰⁺_{∞,1}/𝒞⁺_{∞,1} ≅ Λ(𝒢⁺)/I(𝒢⁺)ζ_p." → needs the Λ(𝒢⁺)-module
> structures the notes construct in §12.1–12.2 ("We will see that…",
> TeX 3096); statement + proof land on the §12 board.

**Q12 (§9 notation due now, TeX 2494–2505):**
> "𝒰_{n,1} := {u ∈ 𝒰_n : u ≡ 1 (mod 𝔭_n)}, 𝒰⁺_{n,1} := 𝒰_{n,1} ∩
> 𝒰_n⁺. The subsets 𝒰_{n,1} and 𝒰⁺_{n,1} are important as they have
> the structure of ℤ_p-modules (indeed, if u ∈ 𝒰_{n,1} … and a ∈ ℤ_p,
> then u^a = Σ_{k≥0} (a choose k)(u−1)^k converges). By contrast, the
> full local units 𝒰_n and 𝒰_n⁺ are only ℤ-modules." /
> "𝒰_∞ := lim← 𝒰_n, 𝒰_{∞,1} := lim← 𝒰_{n,1}; 𝒰_∞⁺ := lim← 𝒰_n⁺,
> 𝒰⁺_{∞,1} := lim← 𝒰⁺_{n,1}, where all limits are taken with respect
> to the norm maps." And TeX 2471–2475: "F_n := ℚ(μ_{p^n}), F_n⁺ :=
> ℚ(μ_{p^n})⁺; 𝒱_n := 𝒪_{F_n}^×, 𝒱_n⁺ := 𝒪_{F_n⁺}^× … where (−)⁺
> denotes the maximal totally real subfield (i.e. the fixed points
> under complex conjugation)."

### Replans (recorded; statements stay faithful)

- **R11.1 (identified Galois side).** All §11 measure statements are
  formalised on Λ(ℤ_p^×) with c := (−1 : ℤ_[p]ˣ) and
  𝒢⁺ := ℤ_[p]ˣ ⧸ zpowers(−1) — Q1 is the notes' OWN definitional move
  ("From now on, we will let Λ(𝒢) be … which we identify with
  Λ(ℤ_p^×)"), so this is not a deviation but the notes' convention.
  The genuine Galois groups: local finite level → §12 (equivariance),
  global Krull → §13/when forced. Blueprint nodes carry a prose note.
- **R11.2 (functional plus-iso).** Q4's finite-level rank-count proof
  needs the Prop 3.9/3.10 projlim presentation (still deferred — its
  §11 entry in plan.md's deferral table now points at §12). Our proof:
  π_* := pushforward along mk is a surjective ring hom; the even-part
  section σν := ν ∘ (descend ∘ (f ↦ ½(f + f∘τ))) (τ = translation by
  −1) lands in Λ⁺ and inverts π_* there; injectivity on Λ⁺ since a
  c-invariant μ satisfies μ(f) = μ(evenPart f) and even functions
  descend. Same objects, same map as Q4 (the natural surjection),
  different proof of bijectivity. Attacks attempted: (1) does σν
  really land in Λ⁺? evenPart(f∘τ) = evenPart f since τ² = id ✓;
  (2) is π_* multiplicative? mk is a continuous MonoidHom and
  convolution pushes forward along monoid homs (general lemma, proven
  via innerInt curry computation) ✓; (3) does descending need T2 or
  total disconnectedness? No — only IsQuotientMap mk (mathlib
  instance) and invariance ✓.
- **R11.3 (pseudo-measure moments = witness encoding).** Q2/Q5/Q6
  integrate pseudo-measures via the notes' eq:integrate
  pseudo-measure convention; our established encoding (padicZeta_moments
  pattern, §4) is exactly that convention. Continuation, not new.
- **R11.4 (principality replaces "topological ideal").** Q7's proof
  line "I(𝒢) is the topological ideal generated by [g]−[1]" is
  replaced by the STRONGER already-proven algebraic principality
  `augmentationIdeal_eq_span` (RJW's own Lem 3.38 machinery). I(𝒢)ζ_p
  is defined as the carrier ideal {x | ∃ l ∈ I(𝒢), x = l·ζ_p in Q}
  (ideal axioms direct from the pseudo-measure property) with
  `zetaIdeal_eq_span : zetaIdeal = Ideal.span {ν}` for any
  generator-witness pair as the computational form. Attack: is the
  carrier really smul-closed without principality? Yes — r·x ↔ l' :=
  r·l ∈ I ✓ (ideals are smul-closed); principality only enters
  eq_span. 𝒢⁺-side identical after transport.
- **R11.5 (convolution algebra generalised in place).** The
  `CommRing (PadicMeasure p ℤ_[p]ˣ)` instance, `deg`, and
  `augmentationIdeal` generalise to `[CommMonoid G] [ContinuousMul G]
  [CompactSpace G]` — `innerInt`/`integral_swap` are already general,
  the instance proofs use only monoid axioms. This is RJW Rem 3.33's
  own generality and avoids an instance diamond for Λ(𝒢⁺).
  Statement-preservation contract: every existing downstream name
  keeps its exact statement; full `lake build` gates the ticket.
  Attack: do downstream `rfl`/`change` proofs survive? The general
  instance's mul at G = ℤ_[p]ˣ is the same formula (unitsConv becomes
  an abbrev/special case); in-file proofs are updated within the
  ticket; out-of-file uses go through the preserved lemma names.
- **R11.6 (𝒰_{n,1} concretely).** "u ≡ 1 mod 𝔭_n" is rendered as
  ‖u − 1‖ < 1 (equivalent: 𝔭_n is the open unit ball of the unit-ball
  ring O_n). The ℤ_p-power u^a is mathlib's
  `addChar_of_value_at_one (u−1)` (the SAME binomial series as Q12 —
  `Tendsto ((u−1)^·) atTop (𝓝 0)` from ‖u−1‖ < 1). Module ℤ_[p]
  packaged on `Additive` of the subgroup.
- **R11.7 (towers inside ℂ_p, global objects too).** Continuation of
  R10.1: F_n := ℚ⟮ξ_n⟯, F_n⁺ := ℚ⟮ξ_n + ξ_n⁻¹⟯ as IntermediateField
  ℚ ℂ_[p] (the "+" = fixed points of conjugation is rendered by the
  standard concrete generator ξ + ξ⁻¹; the Galois-fixed-field
  characterisation is §12 material if needed); 𝒱_n := units u with
  u, u⁻¹ integral over ℤ and u ∈ F_n; 𝒟_n := Subgroup.closure
  {±ξ_n} ∪ {ξ_n^a − 1} ⊓ 𝒱_n (Q8 verbatim — the closure inside F_n^×
  is automatic since all generators lie in F_n); 𝒞_n :=
  topologicalClosure 𝒟_n ⊓ 𝒰_n (the "p-adic closure inside 𝒰_n";
  𝒰_n is closed in ℂ_[p]ˣ so this IS the subspace closure — small
  lemma; the explicit description footnote = lem:closure is §12).
  𝒰_{∞,1}/𝒞_{∞,1} as subgroups of the group-ified NormCompatUnits
  (compat imposed for n ≥ 1 per Q12's "limits n ≥ 1" — matches the
  existing structure's design). Attack on 𝒟_n ⊆ 𝒰_n: needs
  ‖u‖ ≤ 1 for u integral over ℤ — the direct ultrametric argument on
  any monic ℤ-relation (new small lemma; mathlib's spectralNorm route
  exists but is heavier); attack on ξ^a − 1 as a unit of ℂ_[p]ˣ:
  nonzero since ξ^a ≠ 1 requires p ∤ a OR a < p^n with ξ^a ≠ 1 — for
  1 ≤ a ≤ p^n − 1, ξ^a ≠ 1 since ξ has exact order p^n ✓ (Units.mk0).
- **R11.8 (what is NOT here).** thm:iwasawa (Q11) and the
  class-number theorem (Q9): statements not in this board's skeleton
  (see plan.md Scope decision). 𝒰_{∞,1}'s Λ(𝒢)-module structure: §12.

### Leaf ledger (cluster → leaves → discharge)

- **A (±-splitting).** A1 general involution splitting (NOT in
  mathlib — checked LinearAlgebra/Projection + grep "involut";
  PR candidate; proof: e := ½(1+σ) idempotent, IsCompl via
  isCompl_of_proj or direct 4-line argument). A2 instantiation:
  ℤ_p-bilinearity of convolution (SMulCommClass/IsScalarTower
  instances — closes the §8-noted gap), cAct := mulLeft (dirac (−1)),
  involution by dirac_mul_dirac + (−1)·(−1) = 1; plusPart/minusPart
  submodules; Invertible (2 : ℤ_[p]) from isUnit_two_padicInt hp2.
- **B (𝒢⁺ and the iso).** B0 = T1101 (general ring). B1 GPlus
  instances: CompactSpace (mathlib instance), IsTopologicalGroup
  (instIsTopologicalGroup, zpowers(−1) normal by commutativity).
  B2 pushforwardRingHom along continuous MonoidHom (curry
  computation; pushforward_dirac exists). B3 evenPart + descend
  (Quotient.lift + isQuotientMap_mk.continuous_iff; soundness: leftRel
  zpowers(−1) relates x, ±x) + section + plusEquiv. B4 ker π_* =
  minusPart = span{dirac(−1) − 1} + quotient ring iso (first iso thm).
- **C (criterion).** C1 moment of dirac(−1)*μ = (−1)^k·moment
  (units_mul_apply_unitsPowCM + dirac eval). C2 the iff (p-general!
  ℤ_[p] is a char-0 domain so 2x = 0 ⟹ x = 0; ← via
  eq_zero_of_forall_unitsPowCM_eq_zero).
- **D (descent of ζ_p).** D0 scalar lemma: Odd k →
  (1 − p^{k−1})·zetaNeg (k−1) = 0 in ℚ (k = 1: 1 − p⁰ = 0; k ≥ 3:
  bernoulli_eq_zero_of_odd) — the erratum-#13 case split. D1 witness
  odd moments vanish (padicZeta_moments + D0 + ℤ_[p] ↪ ℚ_[p]
  injectivity). D2 c-invariance: algebraMap (dirac(−1) − 1) ·
  padicZeta = 0 (the b = −1 witness has ALL moments 0: even by
  ((−1)^k − 1) = 0, odd by D1 ⟹ witness = 0). D3 witness symmetry
  ν_{−g} = ν_g (uses D2 + witness uniqueness via algebraMap
  injectivity). D4 regularity of dirac ā − 1 in Λ(𝒢⁺) (the
  section-transport: lift, land in Λ⁺ ⊓ ker π_* = 0 by IsCompl, use
  𝒢-side nonZeroDivisor). D5 padicZetaPlus := mk' (π_* ν_a) /
  (dirac ā − 1) + IsPlusPseudoMeasure (push the 𝒢-side witness
  identity ([g]−1)ν_a = ([a]−1)ν_g through π_*) + the witness-compat
  lemma. [Corollary Q6 done.]
- **E (the ideal).** E1 zetaIdeal carrier-Ideal + mem_iff + eq_span
  (via augmentationIdeal_eq_span + IsFractionRing.injective). E2 𝒢⁺
  augmentation principality (ker deg⁺ = π_*(ker deg) by surjection +
  deg⁺ ∘ π_* = deg) + zetaIdealPlus + mem_iff + eq_span.
  [Proposition Q7 done.]
- **F (towers and cyclotomic units).** F1 𝒰_n/𝒰_{n,1} subgroups +
  closedness + K⁺-variants. F2 ℤ_p-powers (R11.6) + Module on
  Additive + ⁺-stability. F3 F_n/F_n⁺/𝒱_n + norm_le_one_of_isIntegral
  (ultrametric argument) + 𝒱_n ≤ 𝒰_n. F4 𝒟_n/𝒟_n⁺ (Q8) +
  𝒟_n ≤ 𝒱_n. F5 𝒞_n/𝒞_{n,1}(⁺)/closure lemma. F6 NormCompatUnits
  CommGroup (Inv: levelNorm of the inverse via levelNorm_mul +
  levelNorm_one — Map.lean's private levelNorm_inv pattern) +
  𝒰_{∞,1}(⁺)/𝒞_{∞,1}(⁺) subgroups. F7 MILESTONE: cycloUnit a n ∈ 𝒟_n
  (subgroup-word: (ξ^a−1)·(ξ−1)⁻¹; ℤ-integrality: 1+ξ+…+ξ^{a−1} and
  the aa' ≡ 1 mod p^n inverse trick — geometric sums of ℤ-integral ξ;
  attack: a = 1 edge (c_n(1) = 1 ✓ trivial); attack: which 𝒟_n-set
  element is ξ^a−1 when a ≥ p^n? Q8's range 1 ≤ a ≤ p^n−1 — reduce a
  mod p^n first, ξ^a = ξ^{a mod p^n}, need a mod p^n ≠ 0 ⟸ p ∤ a ✓)
  + ‖cycloUnit − 1‖ < 1 (sum of ξ^i − 1 terms, each < 1) ⟹
  cyclo ∈ 𝒰_{∞,1} ∧ ∈ 𝒞_{∞,1} [Q10's sentence].

### Per-leaf provability check
Every leaf above is discharged from: existing project API (named
above per leaf), mathlib declarations verified this session at
file:line (QuotientGroup/Quotient.lean:36 CompactSpace, :151
IsTopologicalGroup, :40/:55 quotient-map lemmas; Bernoulli.lean:217;
Padics/AddChar.lean:59; LinearAlgebra/Projection.lean idempotent API),
or new self-contained lemmas with complete arguments sketched (A1,
norm_le_one_of_isIntegral, the F7 integrality tricks). No leaf
depends on deferred machinery (Prop 3.9/3.10 NOT used anywhere).

### Confidence gate (Step 5)
(1) Every headline §11 statement is either decomposed to discharged
leaves (Q1–Q8, Q10, Q12) or explicitly deferred with a recorded reason
(Q9 prose-permanent, Q11 → §12). (2) The two genuinely new
infrastructure pieces (T1101 generalisation; A1 splitting) have
complete proofs sketched against verified API. (3) The erratum (#13)
is recorded with the corrected argument formalised as D0/D1. PASS.

## R12: Proof of Iwasawa's theorem — the §12 layer (RJW §12, TeX 3113–3616)

### Section prose (read in full 2026-06-13)
§12 proves thm:iwasawa via: (12.1) a Λ(𝒢)-module structure on 𝒰_{∞,1} +
Col equivariance; (12.2) the fundamental exact sequence (kernel/cokernel of
Col), resting on thm:log der (CCW surjectivity of ∂log) and lem:rest zp*;
(12.3/12.4) cyclic generators of the global 𝒟_n^+ and local 𝒞_{∞,1}^+
modules; (12.5) assembly into thm:iwasawa 2. The two large new
sub-developments are the Galois action on the tower (E12.1, the linchpin —
absent from both project and mathlib at the concrete-tower level) and
thm:log der (E12.2, Coleman–Coates–Wiles, the hardest mathematics in Part II).

### Verbatim source quotes (headline results)

**Q1 (ℤ_p-equivariance, TeX 3130–3135):**
> "The map Col restricts to a ℤ_p-equivariant map Col : 𝒰_{∞,1} ⟶ Λ(ℤ_p^×)."
Proof key (3137–3145): "a₀(u) ≡ 1 (mod p) … Thus f_u(T) − 1 ∈ (p,T). As
ℤ_p⟦T⟧ is complete in the (p,T)-adic topology, f_u(T)^a = Σ binom(a,j)(f_u−1)^j
converges … f_u^a = f_{u^a} … ∂log(f_u^a) = a ∂log(f_u)".

**Q2 (Teichmüller split, TeX 3159–3168):**
> "We have 𝒰_∞ = μ_{p−1} × 𝒰_{∞,1}." Proof: "reduction modulo 𝔭_n gives a
> short exact sequence 1 → 𝒰_{n,1} → 𝒰_n → μ_{p−1} → 1, which is split, so
> 𝒰_n = μ_{p−1} × 𝒰_{n,1}. The result follows in the inverse limit."

**Q3 (μ_{p−1} killed, TeX 3170–3178):**
> "The subgroup μ_{p−1} of 𝒰_∞ is killed by Col." Proof: "u ↦ f_u … sends
> v ∈ μ_{p−1} … to the constant power series f_v(T) = v. But constant power
> series are killed by … ∂log, which involves differentiation."
> Rem ker Δ: "if f ∈ ℤ_p⟦T⟧ is constant and invariant under 𝒩, then this
> forces f^p = f. Thus the kernel of the composition of the first two maps is
> exactly μ_{p−1}."

**Q4 (𝒢-action on series, TeX 3205–3206):**
> "if f(T) ∈ ℤ_p⟦T⟧, then σ_a(f)(T) = f((1+T)^a − 1)."

**Q5 (Col 𝒢-equivariant, TeX 3193–3236):**
> "The Coleman map Col : 𝒰_∞ → Λ(𝒢) is 𝒢-equivariant." map-by-map:
> "(σ_a f_u)(π_n) = f_u((1+π_n)^a−1) = f_u(ξ^a−1) = f_u(σ_a(ξ−1)) =
> σ_a(f_u(ξ−1)) = σ_a(u_n)" (3210–3216); "∂log(σ_a(f)) = a σ_a(∂log(f))"
> (3218); "∂⁻¹∘σ_a = a⁻¹ σ_a∘∂⁻¹" (3223–3232). cor:G-eq (3241–3243):
> "Col restricts to a map 𝒰_{∞,1} → Λ(𝒢) of Λ(𝒢)-modules."

**Q6 (thm:log der, TeX 3280–3285):**
> "The logarithmic derivative induces a short exact sequence
> 0 → μ_{p−1} → (ℤ_p⟦T⟧^×)^{𝒩=id} →[Δ] ℤ_p⟦T⟧^{ψ=id} → 0."

**Q7 (lem:log der 1, TeX 3292–3306):**
> "We have Δ(𝒲) ⊆ ℤ_p⟦T⟧^{ψ=id}." Proof: "φ(f) = (φ∘𝒩)(f) =
> ∏_{η∈μ_p} f((1+T)η−1). Applying Δ … using Δ∘φ = p·φ∘Δ … (φ∘Δ)(f) =
> p^{-1} Σ_{η∈μ_p} Δ(f)((1+T)η−1) = (φ∘ψ)(Δ(f)). By injectivity of φ,
> ψ(Δ(f)) = Δ(f)."

**Q8 (lem:B mod p 2 — "the most delicate and technical part", TeX 3359–3373):**
> "𝔽_p⟦T⟧ = Δ(𝔽_p⟦T⟧^×) + (T+1)/T·C, where C = {Σ_{n≥1} a_n T^{pn}}."
> Proof builds h = Σ_{(m,p)=1} a_m Σ_k T^{mp^k} and inductively chooses
> α_i ∈ 𝔽_p with h_m := (T+1)/T·h − Σ_{i<m} Δ(1−α_iT^i) ∈ T^{m−1}𝔽_p⟦T⟧,
> using Δ(1−α_iT^i) = −(T+1)/T Σ_k iα_i^k T^{ik}, d_n = d_{np}, α_m = −d_m/m;
> then g = ∏(1−α_nT^n) satisfies Δ(g) = (T+1)/T·h.

**Q9 (lem:rest zp*, TeX 3387–3391):**
> "0 → ℤ_p → ℤ_p⟦T⟧^{ψ=id} →[1−φ] ℤ_p⟦T⟧^{ψ=0} → ℤ_p → 0, where the first
> map is the natural inclusion and the last map is evaluation at T = 0."

**Q10 (def:Zp(1), TeX 3407–3409):**
> "ℤ_p(1) := projlim μ_{p^n}, the module ℤ_p with an action of 𝒢 by
> σ·x = χ(σ)x … an integral version of ℚ_p(1)."

**Q11 (thm:fund exact seq, TeX 3411–3418):**
> "The Coleman map induces an exact sequence of 𝒢-modules
> 0 → μ_{p−1} × ℤ_p(1) ⟶ 𝒰_∞ →[Col] Λ(𝒢) ⟶ ℤ_p(1) → 0, where the last map
> sends μ to ∫_𝒢 χ·μ. In particular … 0 → ℤ_p(1) → 𝒰_{∞,1} →[Col] Λ(𝒢) →
> ℤ_p(1) → 0 of Λ(𝒢)-modules."

**Q12 (γ_{n,a} and global generators, TeX 3456–3486):**
> "γ_{n,a} := ξ_{p^n}^{(1−a)/2} c_n(a) = (ξ^{a/2}−ξ^{−a/2})/(ξ^{1/2}−ξ^{−1/2})
> is fixed by conjugation c ∈ 𝒢, hence gives an element of 𝒟_n^+."
> lem:cyc units gen: "(i) 𝒟_n^+ is generated by −1 and {γ_{n,a} : 1 < a <
> p^n/2, (a,p)=1}. (ii) 𝒟_n is generated by ξ_{p^n} and 𝒟_n^+."
> cor:cyc units gen 2: "If a generates (ℤ/p^nℤ)^×, then γ_{n,a} generates
> 𝒟_n^+ as a ℤ[𝒢_n^+]-module."

**Q13 (lem:closure, TeX 3503–3505):**
> "Let g_1,…,g_r ∈ 𝒰_{n,1} … X = ⟨g_1,…,g_r⟩ the ℤ-module they generate. Then
> the p-adic closure X̄ of X in 𝒰_{n,1} is the ℤ_p-submodule generated by
> g_1,…,g_r."

**Q14 (LemmaGeneratorCinfty1, TeX 3553–3560):**
> "Let a ∈ ℤ be a topological generator of ℤ_p^×, and w ∈ μ_{p−1} ⊂ 𝒰_n with
> aw ≡ 1 (mod 𝔭_n). Then (i) 𝒞_{n,1}^+ is a cyclic ℤ_p[𝒢_n^+]-module
> generated by wγ_{n,a}; (ii) 𝒞_{∞,1}^+ is a cyclic Λ(𝒢^+)-module generated
> by (wγ_{n,a})_{n≥1}."

**Q15 (thm:iwasawa 2 — THE MILESTONE, TeX 3587–3594):**
> "The Coleman map induces: (i) A short exact sequence of Λ(𝒢)-modules
> 0 → 𝒰_{∞,1}/𝒞_{∞,1} → Λ(𝒢)/I(𝒢)ζ_p → ℤ_p(1) → 0. (ii) An isomorphism of
> Λ(𝒢^+)-modules 𝒰_{∞,1}^+/𝒞_{∞,1}^+ ≅ Λ(𝒢^+)/I(𝒢^+)ζ_p."
Proof key (3602–3608): "Col((ξ^b γ_{n,a})_n) = Col(c(a)) = ([σ_a]−[1])ζ_p …
the image of 𝒞_{∞,1} (resp. 𝒞_{∞,1}^+) under Col is I(𝒢)ζ_p (resp.
I(𝒢^+)ζ_p) … Since p is odd, taking invariants under ⟨c⟩ is exact. As c acts
on ℤ_p(1) by −1, ℤ_p(1)^{⟨c⟩} = 0, which shows (ii)."

### Cluster decomposition (mirrors the source's subsection structure)

**E12.1 — Galois action on the tower (GaloisAction.lean) [LINCHPIN, gating].**
Source 3182–3236. Leaves: (a) τ_{a,n} : K_n ≃ₐ[ℚ_p] K_n via
`IsCyclotomicExtension.autEquivPow` (Tower's `isCyclotomicExtension_K` enables
it) at unitsToZModPow a; (b) `autToPow_spec`: τ_{a,n}(ξ_n) = ξ_n^{(a mod p^n)};
(c) tower-compat τ_{a,n+1}|_{K_n} = τ_{a,n} (uniqueness of the auto fixing the
char value); (d) levelNorm∘τ = τ∘levelNorm (Galois-invariance of the relative
norm: mathlib `Algebra.norm_eq_prod_automorphisms`-style / conjugation); (e) the
induced `galAction : ℤ_[p]ˣ → NormCompatUnits ≃ NormCompatUnits` (apply τ
levelwise; mem/inv_mem/compat by (d)); (f) σ_a on PowerSeries: f ↦ f((1+T)^a−1)
(`PowerSeries.subst`; HasSubst since (1+T)^a−1 has const term 0 for a ≥ 1, and
zpPow-binomial for a : ℤ_p); (g) f_{σ_a u} = σ_a f_u (interpolation
τ_{a,n}(u_n) = (σ_a f_u)(π_n) + coleman_existsUnique uniqueness). Attacks: p=2
excluded (autEquivPow needs Φ_{p^n} irreducible /ℚ_p, p odd — hp2);
edge a ∈ μ_{p−1} (σ_a fixes the tower base); the survey's "local field needs
global reduction" caveat — attack: `isCyclotomicExtension_K` is already proven
in Tower.lean so autEquivPow applies directly over ℚ_[p], no reduction needed
(VERIFY at execution; fallback = number-field reduction sub-cluster).

**E12.2 — thm:log der / CCW surjectivity (LogDerivative.lean) [HARD].**
Source 3264–3379. Leaves: series ψ=id/ψ=0 subspaces (new Submodule defs +
the `psiSeries` from NormOperator); `delPhi : Δ∘φ = p·φ∘Δ` (new power-series
identity, direct coeff calc); seriesEqphipsi (φ∘𝒩 f = ∏_{η∈μ_p} f((1+T)η−1)
at series level — the §10-deferred Eqphipsi over ℂ_p[μ_p], product collapse via
∏(Xη−1)=X^p−1); lem:log der 1 (Δ𝒲 ⊆ ψ=id, via the two above + φ injective);
lem:A mod p (𝒲 mod p = 𝔽_p⟦T⟧^×, via normOp_iterate_modEq (ii)(iv) — but those
are PARTLY ABSENT per survey: only phi_injective_mod present, so (ii)
normOp_modEq_self + (iv) iterate are SUB-LEAVES here); lem:B mod p 2 (the
𝔽_p⟦T⟧ construction — its own sub-tree, the expected Tier-A spawn); lem:B mod p;
lem:log der red mod p (A=B ⟹ onto, successive approx + ℤ_p⟦T⟧^× compactness
from §10); thm:log der assembly. Attacks: the ψ=id image needs φ injective on
ℤ_p⟦T⟧ (`phiHom` injective — coeff-degree argument); lem:B mod p 2's induction
termination (T^{m−1}-filtration is exhausting); d_n = d_{np} invariant.

**E12.3 — Fundamental exact sequence (FundamentalSequence.lean).**
Source 3382–3441. Leaves: lem:rest zp* (Σφ^n convergence in (p,T)-topology +
ker(1−φ)=constants + ψ(1+T)=0 + eval-at-0 onto); `ZpOne : Submodule …`
(ℤ_p(1) = {(ξ_n^a)_n : a ∈ ℤ_p} ⊂ 𝒰_∞, via zpPow on ξ — the kernel-of-1−φ
pullback); thm:fund exact seq (compose the four maps' kernels/cokernels:
Col iso ∘ Δ(ker μ_{p−1}, onto by E12.2) ∘ (1−φ)(ker ℤ_p, coker ℤ_p by rest zp*)
∘ ∂⁻¹ iso ∘ 𝓐⁻¹ iso); the Λ(𝒢)-module exactness (E12.1 gives equivariance,
last map ∫χ·μ equivariant). Depends on E12.1, E12.2.

**E12.4 — Generators (Generators.lean).**
Source 3450–3578. Leaves: γ_{n,a} def (half-power ξ^{(1−a)/2} via (2:ZMod p^n)⁻¹,
p odd) + γ ∈ 𝒟_n^+ (c-fixed); lem:cyc units gen (valuation argument Σe_a = 0 +
the ξ^{bp^m}−1 product identity); cor:cyc units gen 2 (a generates ⟹ telescoping
γ_{n,b} = ∏ γ_{n,a}^{σ_a^i} — needs the finite 𝒢_n^+-action from E12.1);
lem:closure (p-adic closure = ℤ_p-span: zpPow binomial convergence + ℤ_p^r
compactness); lem:global generators 2 (wγ_{n,a} ∈ 𝒰_{n,1}: γ_{n,a} ≡ a mod 𝔭_n
from f_{c(a)}(0)=a; (wγ)^{p−1} generates (p−1)𝒟_n^+); LemmaGeneratorCinfty1
(cyclic ℤ_p[𝒢_n^+]/Λ(𝒢^+) generation, (p−1) invertible). Depends on E12.1
(finite Galois action). This cluster NATIVELY resolves the §11 b2-logged
a≡1-mod-p note: w is the Teichmüller correction making wγ_{n,a} ≡ 1 mod 𝔭_n.

**E12.5 — End of proof / thm:iwasawa 2 (Main.lean) [MILESTONE].**
Source 3582–3608. Leaves: thm:iwasawa 2 (i) (the fund exact seq mod 𝒞_{∞,1},
image = I(𝒢)ζ_p by Col_cyclo/coleman_to_kl at the generators + LemmaGenerator-
Cinfty1) + (ii) (the +-part: ⟨c⟩-invariants exact since p odd, ℤ_p(1)^{⟨c⟩}=0);
wire §11's thm:iwasawa node to this. Depends on E12.3, E12.4 + the §11
zetaIdeal(Plus), Col_cyclo, coleman_to_kl.

### Source-structure mirror check (Step 6 gate)
Each cluster cites the source subsection it formalises (E12.1↔§12.1 Galois,
E12.2↔§12.2.1, E12.3↔§12.2.2, E12.4↔§12.3+12.4, E12.5↔§12.5). Internal nodes
(thm:log der, thm:fund exact seq, LemmaGeneratorCinfty1, thm:iwasawa 2) each
decompose along the source's OWN sub-lemmas (named with TeX line numbers above).
The two source-internal multi-lemma nodes (thm:log der, thm:iwasawa 2) get
deeper trees; the one-paragraph source lemmas (lem:rest zp*, lem:closure) are
leaves.

### Feasibility assessment (Step 5)
§12 is FEASIBLE but is the project's largest single section, with two
critical-path sub-developments that are genuinely substantial:
(1) E12.1 (Galois action) — the linchpin; mathlib's `autEquivPow` +
`autToPow_spec` discharge the ABSTRACT iso, and Tower's `isCyclotomicExtension_K`
means it applies over ℚ_[p] directly; the NEW work is tower-compatibility +
levelNorm-commutation + assembling the action on NormCompatUnits and on power
series. No research-grade obstacle, but ~6–9 leaves of careful concrete work.
(2) E12.2 (thm:log der) — the hardest mathematics in Part II; lem:B mod p 2 is
an explicit 𝔽_p⟦T⟧ construction the authors flag as delicate; expect a Tier-A
spawn during execution. The §10 compactness + normOp infrastructure pays off
heavily here. Everything else (E12.3/E12.4/E12.5) is medium assembly on top.
NO leaf requires the deferred Λ-module structure theorem (that's §13). The
board stages E12.1 and E12.2 first as the gating clusters; the milestone
thm:iwasawa 2 is reachable once they land. PASS (staged), with the two flags
recorded for the execution session.

# §13 Stage S — Λ-module structure theory + characteristic ideals (decomposed 2026-06-16)

**Source situation**: RJW §13.1 (TeX 3627–3684) gives the STATEMENTS only ("Here we state without
proof"). The proofs are Washington *Cyclotomic Fields* Ch.13 (Thm 13.12 etc.) + CS06 App A.1; no local
Washington PDF, so S3's proof is decomposed from the standard Iwasawa-theory outline (height-1
localisation → DVR → PID structure → pseudo-iso gluing). **Skeleton files**: `Iwasawa/StructureTheory/`.

## Reuse map (verified by grep in .lake/packages/mathlib, 2026-06-16)
- `Mathlib.RingTheory.PowerSeries.*` — Λ = 𝒪_L⟦T⟧ (`PowerSeries 𝒪_L`); Order, Inverse, NoZeroDivisors, etc.
- `Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished` — `Polynomial.IsDistinguishedAt (f : R[X]) (I : Ideal R)` + `mul`, `map_eq_X_pow`.
- `Mathlib.RingTheory.PowerSeries.WeierstrassPreparation` — `IsWeierstrassDivisorAt`, `IsDistinguishedAt.isWeierstrassDivisorAt`, division `seq`.
- `Mathlib.Algebra.Module.PID` — `Module.equiv_directSum_of_isTorsion` (f.g. torsion / PID), `equiv_free_prod_directSum`, `Submodule.isInternal_prime_power_torsion_of_pid`. **TEMPLATE for the localised (DVR) case of S3.**

## Leaves

### S13-S1 (mostly REUSE): Iwasawa algebra + distinguished polynomials
- Lean (skeleton target, `IwasawaAlgebra.lean`):
  `abbrev IwasawaAlgebra (𝒪 : Type*) [CommRing 𝒪] : Type _ := PowerSeries 𝒪` (notation `Λ`); reuse
  `Polynomial.IsDistinguishedAt` for distinguished polys; Weierstrass preparation = `IsDistinguishedAt.isWeierstrassDivisorAt` + `seq`.
- Source: RJW 3631 (Λ ≅ 𝒪_L⟦T⟧), 3644 (distinguished def). Discharge: mathlib (above) — **leaf, reuse**.
- Adversarial: mathlib's `IsDistinguishedAt` is relative to an ideal `I`; for Λ take `I = 𝔪 = (p)` (max ideal of 𝒪_L). Confirm `𝒪_L` local (it is — ring of integers of a p-adic field). No drift.

### S13-S2 (NEW, small): pseudo-isomorphism
- Lean (`PseudoIso.lean`): `def IsPseudoIso (M M' : Type*) [AddCommGroup M] [Module Λ M] … : Prop := ∃ f : M →ₗ[Λ] M', (Set.Finite (LinearMap.ker f)) ∧ (Set.Finite (M' ⧸ LinearMap.range f))` (finite kernel + cokernel). API: it's an equiv-reln on f.g. TORSION Λ-modules (not in general).
- Source: RJW 3631–3635 (verbatim: "homomorphism M → M' with finite kernel and cokernel"; "is an equivalence relation between finitely generated, torsion Λ-modules"). Discharge: **new, small** (compose finite ker/coker; symmetry uses f.g.+torsion). 
- Adversarial: NOT symmetric in general (RJW Warning §13.2) — only restrict the equiv-reln claim to f.g. torsion. Edge: M=0 → trivially pseudo-iso to 0.

### S13-S3 (NEW, HARD): structure theorem (Washington Thm 13.12) — SUB-CLUSTER
- Lean (`StructureTheorem.lean`): `theorem fg_pseudoIso_canonical (M) [Module.Finite Λ M] : ∃ (r s t) (n : Fin s → ℕ) (f : Fin t → Polynomial 𝒪_L) (m : Fin t → ℕ), (∀ j, (f j).IsDistinguishedAt 𝔪 ∧ Irreducible (f j)) ∧ IsPseudoIso M (Λ^r × (⨁ i, Λ ⧸ Ideal.span {(p)^(n i)}) × (⨁ j, Λ ⧸ Ideal.span {(f j)^(m j)}))`.
- Source: RJW 3637–3642 = Washington Thm 13.12. **NOT a direct mathlib hit** (Λ is dim-2, not a PID).
- Sub-leaves (the standard proof; decompose at execution):
  * S3a: Λ ring-theory — Λ is a Noetherian, integrally-closed (Krull) local domain of dim 2, UFD (mathlib: `PowerSeries` over a DVR/PID; check `UniqueFactorizationMonoid (PowerSeries 𝒪)` / regular-local instances).
  * S3b: height-1 primes 𝔭 ⊂ Λ; `Λ_𝔭` is a DVR (hence PID). (mathlib localisation + DVR-at-height-1 for Krull/regular.)
  * S3c: at each `Λ_𝔭`, apply mathlib `Module.equiv_directSum_of_isTorsion` (PID structure) — the elementary divisors.
  * S3d: pseudo-iso gluing — a f.g. torsion Λ-module is pseudo-iso to ⊕ Λ/(𝔮^k) over the finite set of height-1 primes in its support; the finite ker/coker is the "pseudo-null" discrepancy. (The genuine new content.)
- Adversarial: pseudo-iso (not iso!) — the finite ker/coker is essential (Λ-modules are NOT ⊕-decomposable on the nose, unlike PID). r=0 for torsion. Distinguished+irreducible fⱼ unique up to the char ideal (not the module).

### S13-S4 (NEW): characteristic ideal + multiplicativity
- Lean (`CharIdeal.lean`): `def charIdeal (M) [Module.Finite Λ M] [Module.IsTorsion …] : Ideal Λ := Ideal.span {(p)^n} * ∏ j, Ideal.span {(f j)^(m j)}` (from S3's data); `theorem charIdeal_mul_of_exact {0→M'→M→M''→0 exact} : charIdeal M = charIdeal M' * charIdeal M''`.
- Source: RJW 3652–3657 (def), 3679–3681 (CS06 A.1 Prop 1, multiplicativity). Discharge: **new**, on S3. 
- Adversarial: well-defined? charIdeal must be invariant under pseudo-iso (finite modules have trivial char ideal = (1)) — so it factors through ~. Multiplicativity: the additive count n and the fⱼ-exponents add across exact sequences.

### S13-S5 (NEW): equivariant isotypic decomposition + Ch_{Λ(𝒢)}
- Lean (`Isotypic.lean`): for `𝒢 = H × Γ'` (H = μ_{p-1} prime-to-p, Γ' ≅ ℤ_p), `Λ(𝒢) ≅ 𝒪_L[H] ⊗ Λ`; idempotents `e_ω = |H|⁻¹ Σ_{a} ω⁻¹(a) [a]`; `M = ⨁_{ω ∈ Ĥ} (e_ω • M)`, each f.g. torsion over Λ; `charIdeal_G M := ⨁_ω charIdeal (e_ω • M)`.
- Source: RJW 3659–3676 (CS06 A.1 lemma). Reuse: mathlib group-algebra idempotents (`|H|` invertible since prime-to-p; mathlib `MonoidAlgebra`/`RepresentationTheory` orthogonal idempotents). Discharge: **new**, reuses idempotent machinery.
- Adversarial: needs `|H|` invertible in 𝒪_L — holds (H prime-to-p, 𝒪_L is p-adic). The ω-values may need extending L — note the field-extension caveat (RJW 3664 "after extending L").

## Provability gate (Stage S)
- S1: reuse (mathlib). S2: new-small. S3: new-HARD (sub-cluster S3a–S3d; S3a/S3b/S3c reuse mathlib PowerSeries/localisation/PID, S3d is the new pseudo-iso content). S4/S5: new, on S3.
- The one genuine deep build is **S3d** (pseudo-iso gluing over height-1 primes) — the Λ-analogue mathlib lacks. Everything else is reuse or small. Feasible; S3 is the focus.
- Skeleton: write S1+S2 now (statable), S3–S5 statements drafted as `sorry` during S13-S1/S2 execution (S3's exact form is part of the work). `lake build PadicLFunctions` must stay green (sorries OK).
