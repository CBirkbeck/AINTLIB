# Lane B decomposition — Kedlaya 1410.5160 §2–§4 (PLAN-GATE-1 deliverable)

Produced 2026-07-26 by the beastmode planning pass ("/beastmode on it").
Source of truth: `refs/AdicSpaces/kedlaya-noetherian-ff.txt` (arXiv:1410.5160v3, 901 lines;
line locators below are into that file). Specialization for the campaign: `E = ℚ_p`,
`ϖ_E = p`, `q = p`, `L = F` (the campaign's perfectoid char-p field), so
`W(o_L)_E = W(O_F) = Ainf p F` and `λ_t(Σ pⁿ[xₙ]) = max p^{-n}|xₙ|^t`. We work in the
**untwisted weight parametrization** already used by `GaussNorm.lean`:
`w_ρ = λ_t^{1/t}` with `ρ = p^{-1/t}`, i.e. `w_ρ(Σ pⁿ[aₙ]) = sup_n ρⁿ|aₙ|` — order- and
multiplicativity-equivalent (validated in the 2026-07-26 sol review), so every §2–§4
statement transfers verbatim with `λ_r ↝ w_ρ`, `t ∈ [s,r] ↝ ρ ∈ [ρ_r, ρ_s]` (note the
order reversal `ρ = p^{-1/t}` is decreasing in... CONVENTION: we index intervals directly
by `ρ ∈ (0,1)`, `I = [ρ₁, ρ₂] ⊂ (0,1)`; Kedlaya's `[s,r]`-t-interval corresponds with
endpoints mapped by `t ↦ p^{-1/t}`).

## Frozen architecture decisions (binding for all Lane-B tickets)

**(AD-1) The localizations are plain `Localization.Away`.** Kedlaya's
`A_{L,E} = W(o_L)_E[[x] : x ∈ L]` (Def 2.2, ln 85–92) equals `Ainf[1/[ϖ]]`: every `x ∈ L`
is `a·ϖ^{-k}` with `a = x·ϖ^k ∈ o_L` for large `k`, so `[x] = [a]·([ϖ]^k)⁻¹`, and
conversely `[ϖ]⁻¹ = [ϖ⁻¹]`. Likewise `B_{L,E} = A_{L,E}[1/ϖ_E] = Ainf[1/(p·[ϖ])]`.
Justifying quote (ln 88–90): "each element of A_{L,E} (resp. B_{L,E}) can be written
uniquely in the form Σ_{n∈ℤ} ϖⁿ[xₙ] for some xₙ ∈ L which are zero for n < 0 (resp. for
n sufficiently small)". So: `Aloc := Localization.Away (teichPi p F ϖF)`,
`Bloc := Localization.Away ((p : Ainf p F) * teichPi p F ϖF)` for a FIXED pseudo-
uniformizer `ϖF` normalized as in (AD-4).

**(AD-2) The norms are `Valuation.extendToLocalization` of `gaussVal`.** `λ_t` on
`B_{L,E}` (formula (2.2.1), ln 92–95) is the unique multiplicative extension of the Gauss
value; since `gaussVal` is multiplicative (T803) and nonvanishing on `p·[ϖ]`-powers
(`gaussValue_p_teichPi_ne_zero`), mathlib's `Valuation.extendToLocalization` applies, and
`extendToLocalization_mk'` gives `w(x/(p[ϖ])^k) = w(x)/(ρ|ϖ|)^k`. The family
`{wLoc ρ : Valuation Bloc ℝ≥0, ρ ∈ (0,1)}` replaces Kedlaya's `{λ_t}`.

**(AD-3) `A^r` is a CONCRETE subring of `W(F)`, not an abstract completion.** Kedlaya
himself works with the series realization (Def 2.4, ln 100–106): "A^r_{L,E} maps into
W(L)_E; more precisely, if we write an arbitrary element x ∈ W(L)_E as a p-adically
convergent sum Σ ϖⁿ[xₙ], then x ∈ A^r iff p^{-n}|xₙ|^r → 0 as n → ∞. Moreover, the
formula (2.2.1) continues to hold". The Euclidean/Gröbner constructions (Lemma 2.8's
`z_l = Σ ϖⁿ[y_{l,n+m}/x_m]`, ln 152–156; Lemma 3.8's iterations) are coefficientwise
series surgery — natural on a concrete carrier, hopeless through an abstract completion.
So: `Ar ρ := {x : WittVector p F | Tendsto (fun n => ρⁿ·|teichCoeff x n|) atTop (𝓝 0)}`
as a subring of `W(F)` (F perfect ⟹ all mathlib Witt machinery applies), with
`wAr ρ x := ⨆ n, ρⁿ|xₙ|` (a MAX: attained, by decay + the T801 argument). The GaussNorm
engines (pair bound, head split, scaling, level-rep, CORE-1/2) generalize from `W(O_F)`
to `W(F)` — the u-trick needs only `v(b) ≤ v(a) ⟹ b/a ∈ O_F`, which is valuation-theoretic
and entry-ring-agnostic; the boundedness hypotheses become the decay conditions. This
generalization is its own ticket (T902) and REPLACES `≤ 1`-boundedness by
max-attainment everywhere.
  - Ring-closure of the carrier (sums/products stay decaying) comes from the generalized
    level-rep/pair bounds, NOT from polygon arguments.
  - Completeness of `Ar` under `wAr` is deferred: NOT needed for §2–§3 (division and
    Gröbner only need: series realization, attainment, and closure under the explicit
    limit-constructions in 2.8/2.9/3.8/3.9, each of which is a coefficientwise convergent
    construction handled by a dedicated summability lemma, T903). Record: Kedlaya also
    never uses abstract completeness beyond "the sum converges" in these proofs
    (Prop 2.9, ln 208–216: "λ_r(z_l) ≤ ... → 0 and the sum again converges").
  - `Br ρ := Ar ρ [1/p]` is again `Localization.Away` (Def 2.4, ln 100: "B^r = A^r[ϖ⁻¹]").

**(AD-4) Normalization `|ϖF| = p⁻¹`, all interval endpoints in `p^ℚ`.** Fix once
`ϖF : PseudoUniformizer F` with `|ϖF| = p⁻¹`... F's value group need not contain p⁻¹
exactly; INSTEAD: fix `ϖF` arbitrary, put `c := |ϖF| ∈ (0,1)`, and use `c` as the base:
all interval endpoints and Tate-algebra radii are taken in `c^ℚ`. Since `F` is perfect,
`ϖF^{a/b} ∈ F` exists for all `a/b ∈ ℚ`, and `[ϖF^{a/b}]` is a UNIT of `Ar` with
`wAr ρ ([ϖF^{a/b}]) = c^{a/b}`. (Kedlaya's `ρ ∈ p^ℚ` side conditions in Lemma 4.9,
ln 442–447, play exactly this role.)

**(AD-5) Weighted Tate algebras via rescaling — reuse `RestrictedPowerSeries`.**
Kedlaya needs `A^r{T₁/ρ₁,...}` for arbitrary ρᵢ (Def 3.1, ln 246–258; Rem 4.11, ln 471–476
explains why ρ ≠ 1 is unavoidable: "we need to allow arbitrary ρ in order to fix the left
endpoint of the interval I using Lemma 4.9"). For radii in `c^ℚ` (all we need, by AD-4),
`A{T/ρ} ≅ A{T}` isometrically via `T ↦ [ϖF^{a/b}]·T` because the rescaling factor is a
unit of the coefficient ring with exact norm ρ. So Lane B states everything for the
repo's existing `A⟨X₁..Xₖ⟩` (`RestrictedPowerSeries`) over `Ar`, plus a rescaling-iso
lemma; no new weighted-Tate-algebra theory. THE STATEMENT of Thm 3.2/4.10 we prove is
therefore: noetherianity of `Ar⟨X₁..Xₖ⟩` and `BI⟨X₁..Xₖ⟩` (Huber's strongly-noetherian,
= the repo's `IsStronglyNoetherian`), which is the ρ=1 case — combined with AD-4/AD-5
rescalings wherever Lemma 4.9 needs a non-unit radius.

**(AD-6) NO Newton polygons on the critical path.** `deg` is DEFINED as the largest
max-attaining index (Kedlaya's primary definition, Def 2.5 ln 115–118: "the degree of x
[is] the largest n realizing λ_r(x) = max p^{-n}|xₙ|^r"). Its two needed properties:
  - additivity `deg(xy) = deg x + deg y` (Lemma 2.6, whose polygon proof is omitted in
    the source, ln 124–127): proved instead by the T803 MIRROR argument — split at the
    LARGEST attaining index, tail strictly smaller (only finitely many terms above any
    threshold), leading product term `x_{j}·y_{k}` exact, isosceles;
  - stability `λ_r(x−y) < λ_r(x) ⟹ deg x = deg y` (Rem 2.7, ln 137–139): direct from
    attainment + ultrametric.
  Polygons/multiplicities (Def 2.5's second half, Lemma 4.8, §6–§8) are NOT needed for
  Thm 3.2 + Lemma 4.9 + Thm 4.10 and are out of Lane-B scope.

**(AD-7) `B^I` is the abstract two-norm completion, coefficients recovered as
theorems.** `λ_I = max{λ_s, λ_r}` is only power-multiplicative (Def 4.2, ln 335–338), so
no `Valued`-instance; `BI` is the `SeminormedRing`-completion of `Bloc` under
`max(wLoc ρ₁, wLoc ρ₂)` (mathlib normed-ring completion; the repo's
SpaRationalOpenComparison pattern shows the Completion-ring toolkit in action). The
series realization on `BI` (needed for Lemma 4.9's computations) is recovered via the
**coordinate-continuity lemma** (Hölder, NOT Lipschitz: coordinates at level n are
p^n-homogeneous, so `|aₙ − bₙ| ≲ (ρ^{-n}·w(a−b))^{p^{-n}}`) — source: Kedlaya 1004.0466
Theorem 4.5 (the continuity of λ; `refs/AdicSpaces/kedlaya-new-methods.txt` ln ~1040+),
transcribe its proof when implementing T908.

## The decomposition tree (tickets T901–T912)

Each leaf carries its source locator; quotes are in the ticket bodies on the board.

```
Thm 4.10 (BI strongly noetherian)                                [T912]
├── Thm 3.2 (Ar⟨X₁..Xₖ⟩ noetherian)                              [T907]
│   ├── Gröbner data: monomial WQO + graded-lex (Def 3.4)        [T905, mathlib?]
│   ├── leading index/coefficient on Ar⟨X⟩ (Def 3.6)             [T905]
│   ├── the Gröbner set S is finite (Def 3.7, Dickson)           [T905]
│   ├── Lemma 3.8 (approximate generation, ε-iteration)          [T906]
│   │   └── Prop 2.9 (Euclidean division in Ar)                  [T904]
│   │       └── Lemma 2.8 (approximate division, ε-iteration)    [T904]
│   │           ├── (2.8.1) n-ary Teichmüller sum estimate       [T902 engine]
│   │           └── deg + Rem 2.7 + attainment                   [T903]
│   └── Lemma 3.9 (exact generation, geometric limit)            [T907]
├── Cor 2.10 (Ar Euclidean ⟹ PID)                                [T904 tail]
│   └── deg-additivity (Lemma 2.6, T803-mirror proof)            [T903]
├── Lemma 4.9 (quotient presentations of B^I)                    [T910, T911]
│   ├── λ_I, BI, BI⁺; three-circles (L4.4), λ_I = sup (C4.5)     [T908]
│   ├── coordinate-continuity (1004.0466 Thm 4.5)                [T908]
│   └── restriction maps (C4.6)                                  [T909]
└── carriers: Bloc/wLoc [T901]; Ar/W(F)-engines [T902]; Br [T903 tail]
```

Ticket statements + full sketches are on the board (tickets.md, T901–T912).

## Feasibility notes

- T901 is pure plumbing on verified mathlib API (extendToLocalization) — start here.
- T902 is the load-bearing generalization (GaussNorm engines from `O_F`-entries to
  decaying `F`-entries). Everything in GaussNorm.lean was deliberately factored through
  `teichCoeff`, `exists_head_split`, `exists_level_rep`, so the port is mechanical but
  large. Risk: the fold/level-rep bounds must be re-derived with `max`-attained sups
  instead of `≤ 1` bounds.
- T904 (division) and T906 (Gröbner approximate generation) are the two ε-iterations —
  the genuinely hard proofs, both with explicit strictly-decreasing ℕ-quantities
  (N_l in 2.8, the ≺-argument in 3.8): well-founded recursion, no choice needed.
- The B3-bar (published-theorem scale) does not apply: the user explicitly directed the
  campaign at this paper ("the reference is kedlayas paper: Noetherian properties of
  Fargues-Fontaine curves which is what we need to prove").
