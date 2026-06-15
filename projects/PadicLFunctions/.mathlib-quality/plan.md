# Development Plan: §3 Measures and Iwasawa algebras (arXiv:2309.15692)

## Goal

Formalise the measure-theoretic foundations of the Kubota–Leopoldt construction,
§3.2–3.6 of Rodrigues Jacinto–Williams (RJW), *An introduction to p-adic
L-functions* (source TeX: `.mathlib-quality/references/2309.15692-padic-L-functions.tex`,
lines 671–1287). Headline targets, in Lean form:

1. `PadicMeasure p X := C(X, ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]` for `X` compact, with automatic
   continuity/boundedness (RJW Def 3.6 `def:measures` + the O_L-integrality convention).
2. `mahlerRingEquiv : PadicMeasure p ℤ_[p] ≃+* PowerSeries ℤ_[p]` — the Mahler/Amice
   transform as a ring isomorphism (RJW Thm 3.20 `thm:mahler`).
3. The measure-theoretic toolbox (RJW §3.5): multiplication by `x` ↔ `(1+T)d/dT`,
   restriction to clopens, `σ_a`, `φ`, `ψ`, `ψ∘φ = id`, `φ∘ψ = Res_{pℤ_p}`,
   `Res_{ℤ_p^×} = 1 − φψ`, and `supported on ℤ_p^× ↔ ψ = 0` (RJW Cor 3.32).
4. Pseudo-measures on `ℤ_p^×` (RJW §3.6): convolution ring `Λ(ℤ_p^×)`, the
   zero-divisor lemma (RJW Lem 3.36 `lem:zero divisor`), augmentation ideal, and
   `μ/([a]−[1])` is a pseudo-measure (RJW Lem 3.38 `lem:pseudo-measure existence`).

## References

- [RJW] = arXiv:2309.15692v2, §3 (lines 671–1439 of the TeX). All source quotes in
  `decomposition.md` cite TeX line numbers from this file.
- [Colmez] Colmez, *Fonctions d'une variable p-adique* (RJW's own reference for §3;
  mathlib's `MahlerBasis.lean` also follows it). Not needed directly — mathlib covers
  the analytic input.

## Mathlib Inventory (all names verified by reading the source in `.lake/packages/mathlib`)

| Concept | Mathlib status | Our action |
|---|---|---|
| ℤ_p, ℚ_p, completeness, `denseRange_natCast`, `isUnit_iff`, `toZModPow`, `ker_toZModPow`, `appr` | `NumberTheory.Padics.{PadicIntegers,RingHoms}` | USE |
| Mahler basis `mahler k : C(ℤ_[p], ℤ_[p])`, `hasSum_mahler`, `fwdDiff_tendsto_zero`, `mahlerSeries`, `fwdDiff_mahlerSeries`, `mahlerEquiv`, `norm_mahler_eq` | `NumberTheory.Padics.MahlerBasis` | USE (this is RJW Thm 3.13 in full) |
| `Δ_[h]` forward differences | `Algebra.Group.ForwardDiff` | USE |
| `BinomialRing ℤ_[p]`, `Ring.choose`, Chu–Vandermonde `add_choose_eq` (line 519), `descPochhammer_eq_factorial_smul_choose` (line 390) | `RingTheory.Binomial` | USE |
| `(1+X)^r` as `PowerSeries.binomialSeries`, `binomialSeries_add`, `binomialSeries_coeff` | `RingTheory.PowerSeries.Binomial` | USE |
| `PowerSeries.subst`, `substAlgHom`, `HasSubst.of_constantCoeff_zero'` | `RingTheory.PowerSeries.Substitution` | USE for σ_a, φ (const coeff 0 ✓) |
| `PowerSeries.derivativeFun` | `RingTheory.PowerSeries.Derivative` | USE for `∂ = (1+T)d/dT` |
| Sup-norm ring structure on `C(X, R)`, X compact; `ContinuousMap.isUltrametricDist` | `Topology.ContinuousMap.Compact`, `Topology.MetricSpace.Ultra.ContinuousMaps` | USE |
| `ContinuousMap.curry` | `Topology.CompactOpen` (line 419) | USE for convolution |
| `LocallyConstant`, `charFn` (clopen indicator) | `Topology.LocallyConstant.{Basic,Algebra}` | USE |
| Density of locally constant in `C(X, ℤ_[p])`, X compact | **MISSING** | DEFINE+PROVE (leaf L1.4; RJW proves it at lines 782–802) |
| p-adic measures, Amice/Mahler transform of measures, convolution algebra, Iwasawa algebra, pseudo-measures | **MISSING** (no `Amice`/Iwasawa-algebra/Kubota–Leopoldt hits) | THE PROJECT |
| `CompactSpace ℤ_[p]ˣ` | **MISSING** (Units topology exists in `Topology.Algebra.Constructions`) | PROVE (leaf L5.1) |
| `IsCyclic (ZMod (p^n))ˣ`, p odd | `RingTheory.ZMod.UnitsCyclic` `isCyclic_units_of_prime_pow` (line 198) | USE |
| `MonoidAlgebra` over comm ring/group | `Algebra.MonoidAlgebra.*` | USE for finite levels |
| Nested compact intersection | `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed` | USE for the inverse-limit step of Lem 3.38 |
| `FractionRing` (localisation at non-zero-divisors) | `RingTheory.Localization` | USE for Q(ℤ_p^×) |

## File Structure (build order)

- `PadicLFunctions/Measure/Basic.lean` — `PadicMeasure`, auto-continuity, Dirac,
  pushforward along continuous maps, locally-constant density + ext.
- `PadicLFunctions/Measure/MahlerTransform.lean` — `mahlerCoeff`, `mahlerTransform`,
  evaluation formula, injectivity, inverse, `mahlerLinearEquiv`, `𝓐(δ_a) = (1+T)^a`.
- `PadicLFunctions/Measure/Convolution.lean` — `CommRing (PadicMeasure p ℤ_[p])` by
  transport along `mahlerLinearEquiv` (RJW line 908 "by transport of structure"),
  `mahlerRingEquiv`, the convolution formula `mul_apply` (Chu–Vandermonde), Diracs.
- `PadicLFunctions/Measure/Toolbox.lean` — mult-by-x ↔ ∂, eval at x^k, Res, σ_a, φ, ψ
  and all identities of RJW §3.5 that stay over ℤ_p.
- `PadicLFunctions/Measure/UnitsZp.lean` — `CompactSpace ℤ_[p]ˣ`, val is closed
  embedding with clopen range, extension-by-zero, ι : Λ(ℤ_p^×) ↪ Λ(ℤ_p), image = ker ψ.
- `PadicLFunctions/Measure/PseudoMeasure.lean` — convolution ring on `Λ(ℤ_p^×)`
  (Fubini-for-duals via locally-constant box decomposition), degree map, augmentation
  ideal, finite-level maps, zero-divisor lemma, pseudo-measures, RJW Lem 3.38.

## Dependency Graph

```
Basic ──→ MahlerTransform ──→ Convolution ──→ Toolbox ──→ UnitsZp ──→ PseudoMeasure
  └──────────────(density, pushforward used throughout)─────────────────┘
```

## Generality Decisions

1. **Coefficients = ℤ_p (not O_L) in this pass.** RJW fixes a finite `L/ℚ_p` once, but
   every object through §4 (the measures `μ_a`, θ_a, ζ_p) is ℤ_p-valued; larger
   coefficients are first *needed* in §5 (Dirichlet characters of conductor p^n, Gauss
   sums). Decision: develop §3 over ℤ_p; run a dedicated generalisation pass
   (`/generalise`) to `𝒪_L` when the §5 /develop pass starts. Risk recorded: the
   statements have been designed so the generalisation is parameter-insertion, not
   redesign (the Mahler input `mahlerEquiv` is already stated for general normed
   ℤ_[p]-modules `E`).
2. **`X` arbitrary (compact) where possible.** `PadicMeasure p X` is defined for any
   topological `X`; compactness is assumed per-lemma. This matches RJW's remark (line
   768–770) that the definitions apply to any subset of `G`.
3. **Ring structure on Λ(ℤ_p) by transport** along the Mahler equivalence — RJW's own
   words (line 908: "by transport of structure"); the convolution integral formula is
   the "one checks" theorem, proved on the Mahler basis via Chu–Vandermonde + density.
4. **Λ(ℤ_p^×) by direct convolution** (the group is multiplicative, so no `to_additive`
   gymnastics; ℤ_p never needs the direct convolution definition).

## Deferred (recorded so nothing is silently dropped)

| Item | Source | Why deferred | Where it lands |
|---|---|---|---|
| §3.1 Banach prelims (valuations, orthonormal bases, dual topologies) | lines 680–744 | mathlib's normed-space + `mahlerEquiv` supply everything these anchor; RJW says §3.1 "may be skipped" | not formalised; blueprint nodes stay prose |
| `M(G,O) ≅ projlim O[G/H]` for profinite G + Iwasawa-algebra-as-limit (Props 3.9/3.10) | lines 850–921 | not needed for §4–5: Λ(ℤ_p) ≅ ℤ_p[[T]] is proved directly (the source's own thm:mahler proof); finite-LEVEL maps (not the full limit) suffice for Lem 3.38 | Part II pass (§11, measures on Galois groups) |
| Additive-functions-on-clopens description (Rem 3.7/3.8) | lines 782–829 | only its locally-constant-density ingredient is needed now (L1.4); the clopen-additive-function equivalence is pulled in by the Part II pass | Part II pass; density leaf done NOW |
| z-twist power-series formula `𝓐(z^x μ) = 𝓐μ((1+T)z−1)` and ξ-restriction formulas `EqRestrictionFormula`/`Eqphipsi` | lines 1084–1158 | substitution at non-nilpotent constant term + coefficients in ℤ_p[μ_{p^n}] ⊄ ℤ_p: both need the O_L pass. All §3–4 identities that *use* them have ξ-free measure-side proofs (planned as such) | §5 interpolation pass |
| §3.7 locally analytic functions/distributions | lines 1287–1439 | RJW: "may be safely skipped on a first reading"; first used in §6–7 | §6–7 pass |

## ChatGPT validation

`ask_chatgpt_math` not available in this session — skipped per the skill.

## §4 addendum (2026-06-10) — Kubota–Leopoldt

### Mathlib inventory (§4-specific, all grep-verified at file:line)
| Concept | Mathlib status | Our action |
|---------|---------------|------------|
| Bernoulli gen. function | `bernoulliPowerSeries_mul_exp_sub_one` (Bernoulli.lean:273) | USE |
| `B_odd = 0` | `bernoulli_eq_zero_of_odd` (:217) | USE |
| `ζ(−n)` complex | `riemannZeta_neg_nat_eq_bernoulli` (HurwitzZetaValues) | USE (bridge file only) |
| `exp`, `e^{at}` | `PowerSeries.exp`, `exp_pow_eq_rescale_exp` (Exp.lean:153) | USE |
| Chain rule for subst | `PowerSeries.derivative_subst` (Derivative.lean:184) | USE |
| `constantCoeff_subst` | Substitution.lean:244 | USE |
| PS unit ⟺ const unit | `isUnit_iff_constantCoeff` (Inverse.lean:111) | USE |
| ℕ coprime p unit in ℤ_p | not found | DEFINE `PadicInt.isUnit_natCast_of_not_dvd` (PR candidate) |
| Λ(ℤ_p) domain | — | DEFINE instance via `mahlerRingEquiv` transport |
| projection formula ψ(φν·μ)=ν·ψμ | — | DEFINE (`psi_phi_mul`) |
| integer top. generator | — | DEFINE `exists_nat_topological_generator` (Washington §3 classical) |

### §4 design decisions
- **ζ-values**: `zetaNeg k := (−1)^k bernoulli (k+1)/(k+1) : ℚ` (TeX 1455's own
  formula); all interpolation in ℚ_p via `Rat.cast`; complex bridge quarantined in
  `ZetaValuesComplex.lean`. `kl-values-of-zeta` blueprint node unwired until §2
  Mellin theory.
- **F_a**: defined by clearing denominators — `Fa := ((geomSum−a)/X)·Ring.inverse
  geomSum`, characterised by `((1+X)^a−1)·Fa = geomSum − a`. Junk-total defs,
  `hpa : ¬ p ∣ a` on lemmas.
- **ψ-invariance replan** (T034): source's ξ/μ_p-proof replaced by projection
  formula + finite Dirac identities (decomposition R3 block) — keeps the deferred
  O_L/ξ cluster deferred.
- **delQ debt**: ℚ_p-clone of `del`; merge by generalising `del` to `CommRing R`
  in a cleanup pass (do not churn §3 mid-section).
- **a : ℕ** parametrisation for μ_a (source: "integer coprime to p"); the
  topological-generator integrality gloss of Def 4.10 is made explicit
  (`exists_nat_topological_generator`, p ≠ 2).

### Deferred (unchanged from §3 + one §4 note)
- ξ/roots-of-unity `Eqphipsi`, O_L coefficients → §5 pass (T034's replan keeps
  this deferral intact).
- §2 Mellin/L(f_a,s) analytic continuation → §2 chapter pass
  (`kl-values-of-zeta` wiring blocked on it).

## §5 addendum (2026-06-10) — Interpolation at Dirichlet characters (TeX 1610–1979)

### Mathlib survey B + §5-specific (all grep-verified at file:line in the pinned mathlib)

| Concept | Mathlib status | Our action |
|---------|---------------|------------|
| `DirichletCharacter R N`, `conductor`, `IsPrimitive`, `changeLevel`, `primitiveCharacter`, `Even/Odd`, `FactorsThrough` | `NumberTheory/DirichletCharacter/Basic.lean` (221–301, 418–427) | USE |
| Gauss sum `gaussSum χ ψ` | `NumberTheory/GaussSum.lean:72` | USE |
| Rem 5.3(ii) `G(χ) = χ(a)Σχ(c)ε^{ac}` | `gaussSum_mulShift` (GaussSum.lean:76), **`gaussSum_mulShift_of_isPrimitive`** (DirichletCharacter/GaussSum.lean:57 — all `a`, incl. non-units) | USE |
| Rem 5.3(i) `G(χ)G(χ⁻¹) = χ(−1)p^n` | only field-level `gaussSum_mul_gaussSum_eq_card` (GaussSum.lean:145; `ZMod p^n` is not a field for n ≥ 2) | **DEFINE+PROVE at general level N for primitive χ** (PR candidate; route: Ramanujan-sum/unit-sum split, ingredients `AddChar.sum_mulShift`-style all present) |
| Dirichlet L-function (analytic continuation) | `DirichletCharacter.LFunction` = `ZMod.LFunction` = Hurwitz combination (DirichletContinuation.lean:61, ZMod.lean:83) | USE (complex bridge only) |
| Hurwitz zeta at −k via Bernoulli polynomials | `hurwitzZeta_neg_nat` (HurwitzZetaValues.lean:189) | USE → derive `L(χ,−k) = −B_{k+1,χ}/(k+1)` complex-side (quarantined bridge file, ZetaValuesComplex-pattern) |
| Generalised Bernoulli numbers `B_{k,χ}` | **MISSING** | DEFINE in the coefficient field via `Polynomial.bernoulli` (BernoulliPolynomials.lean), with API |
| Mahler basis for general coefficients | `PadicInt.mahlerEquiv : C(ℤ_[p], E) ≃ₗᵢ[ℤ_[p]] C₀(ℕ, E)`, E any `[NormedAddCommGroup] [Module ℤ_[p]] [IsBoundedSMul] [IsUltrametricDist] [CompleteSpace]` (MahlerBasis.lean:356) | USE — this is the O_L-widening input; §3 dual-side arguments re-run verbatim |
| Continuous additive characters of ℤ_p / `(1+r)^x` | **`PadicInt.addChar_of_value_at_one`, `continuousAddCharEquiv`** for complete ultrametric normed ℤ_[p]-algebras (Padics/AddChar.lean:59,102) | USE — gives ξ-characters `x ↦ ξ^x` AND `⟨x⟩^s` (§5.3) for free |
| Topological power-series substitution `F((1+T)ξ−1)` | `PowerSeries.eval₂/aeval`, `HasEval = IsTopologicallyNilpotent` (PowerSeries/Evaluation.lean), needs `IsLinearTopology S S` + complete | USE for ξ-formulas if/where the paper route is taken (instance plumbing on `O_L⟦T⟧` w/ `WithPiTopology` to verify); measure-side ξ-free replans otherwise |
| ℂ_p, Q̄_p | `PadicComplex`, `PadicAlgCl` + `𝓞_ℂ_[p]` (Padics/Complex.lean) | available as ambient for root-of-unity systems |
| p-adic exp/log (Lem 5.14) | **MISSING** (no p-adic exp/log in mathlib) | REPLAN: `⟨x⟩^s` via `addChar_of_value_at_one` (binomial/character route, no exp); Lem 5.14's exp statement stays a prose node (or own API-gap cluster if user wants it literal) |
| Teichmüller ω | `Perfection.teichmuller` (RingTheory/Teichmuller.lean, perfection-based — extraction friction for ℤ_p) | DEFINE directly (`ω(x) = lim x^{p^n}`, Cauchy by Fermat+binomial; small API: value-roots-of-unity, ≡ x mod p, multiplicative, section of reduction) |
| Valuations | `ValuativeRel` (RingTheory/Valuation/ValuativeRel/Basic.lean:74) + Padics instances | blueprint-link only (§3.1 prelims) |
| measure-side Mahler/Amice | still **MISSING** in mathlib (no overlap with §3) | project stays novel |

### §5 design decisions (Generality)
1. **Coefficient widening (rule-6 break, planned cluster):** parametrise
   `PadicLFunctions/Measure/*` by a coefficient ring `R` with exactly the
   `mahlerEquiv`/`Padics.AddChar` typeclass set — `[NormedCommRing R]
   [Algebra ℤ_[p] R] [IsUltrametricDist R] [CompleteSpace R]` (+ `NormMulClass R`,
   `IsDomain R` per-lemma where needed); ℤ_p-specific proofs (T001-style
   norm-attainment) re-attacked at decomposition. §4 files stay instantiated at
   `R := ℤ_[p]` — no churn. The paper's "fixed finite L/ℚ_p, coefficients O_L"
   instantiates R := 𝓞_L; scalar-extension Λ_{ℤ_p}(X) → Λ_R(X) is the power-series
   coefficient-inclusion under Mahler.
2. **χ valued in the coefficients:** `χ : DirichletCharacter L (p^n)` with L the
   p-adic coefficient field (NOT ℂ) — B_{k,χ} ∈ L directly; complex statements
   quarantined in a bridge file via an L ↪ ℂ embedding (ZetaValuesComplex pattern).
3. **Twist μ_χ defined measure-side** (∫f·μ_χ = ∫χ̃f·μ, χ̃ the locally constant
   zero-extension through `toZModPow`) — no roots of unity in the definition; the
   ξ-expression for 𝓐_{μ_χ} (Lem 5.4 / EqRestrictionFormula) is then a theorem.
4. **ξ-machinery vs ξ-free**: paper route preferred (user directive); where the
   paper's computation passes through objects our Λ lacks (Laurent 1/T) or needs
   μ_{p^n} ⊂ L hypotheses a statement doesn't, the T034 projection-formula pattern
   (`psi_phi_mul` + Dirac telescopes, e.g. ψ(F_η) = η(p)F_η via the geometric
   factorisation ((1+T)^pε^{pc}−1) = ((1+T)ε^c−1)·Σ_{j<p}((1+T)ε^c)^j) is the
   recorded replan. Decided leaf-by-leaf in decomposition.md with quotes.
5. **§5.3**: ω by direct limit construction; `⟨x⟩^s` via `addChar_of_value_at_one`;
   ζ_{p,i}/L_p(θ,s) as functions on ℤ_p (analyticity deferred with §3.7 to §6–7);
   p odd structural throughout (μ_{p−1}×(1+pℤ_p) decomposition).

### flt-regular-bernoulli survey (user request, 2026-06-10)

Surveyed `~/Documents/GitHub/flt-regular-bernoulli` (the user's own Kummer-criterion
project, `BernoulliRegular/`, 0 sorries, axiom-clean) for portable Bernoulli results.

| Their asset | Content | Decision |
|---|---|---|
| `Characters.lean` (~340 LOC) | `teichmuller p : ZMod p →*₀ ℤ_[p]` via mathlib `Perfection.teichmuller₀` + `PadicInt.residueField`; API: `toZMod_teichmuller` (ω(a) ≡ a mod p), `teichmuller_pow_sub_one`, `isUnit_teichmuller`, `teichmuller_injective`, `teichmuller_pow_card` (Frobenius-fixed), mod-p² congruence, `teichmullerChar : DirichletCharacter ℤ_[p] p`, `orderOf_teichmullerChar = p−1`, `HasEnoughRootsOfUnity ℤ_[p] (p−1)`, `IsCyclic (DirichletCharacter ℤ_[p] p)`, parity lemmas (`teichmullerChar_odd`, `_pow_even_iff`) | **PORT for T517** (supersedes the survey-table row "DEFINE directly" and design decision 5's "ω by direct limit construction"). Source-faithful: mathlib's `Perfection.teichmullerFun` IS the limit-of-`p^n`-th-powers-of-lifts construction (`teichmullerAux`), i.e. RJW Def 5.15's `lim x^{p^n}` route, packaged through the perfection of the residue field. Both `Mathlib.RingTheory.Teichmuller` (`teichmuller₀`, `mk_teichmuller₀`) and `PadicInt.residueField` exist in our pin — verified. Port shape: `PadicInt.teichmullerZMod : ZMod p →*₀ ℤ_[p]`, then skeleton `teichmullerFun p x := teichmullerZMod p (toZMod x)`; all 6 skeleton sorries follow from the ported API. Their `module`/`public import` syntax stripped to plain imports; `BernoulliRegular` namespace → `PadicInt`. |
| `BernoulliGeneralized.lean` (622 LOC) | `BernoulliGen` (ZMod-sum, ℕ-sub convention — agrees with our `genBernoulli` for **nontrivial** χ; differs at trivial χ where ours matches Washington/`bernoulli'`); `natCast_mul_BernoulliGen_one_of_ne_one` (N·B₁,χ = Σ χ(a)·a.val); `teichmullerCharQp := (teichmullerChar p).ringHomComp PadicInt.Coe.ringHom` + order lemmas; `bernoulliGen_teichmuller_inverse_eq_p_sub_one_div_p_add_padicInt` (B₁,ω⁻¹ = (p−1)/p + p-integral); von Staudt–Clausen cluster (`bernoulli_mem_padicInt_of_lt_sub_one`, `prime_not_dvd_bernoulli_den_of_lt_sub_one`, `bernoulli_pSubOne_add_inv_p_mem_padicInt`) | **Reference for T520 + §6/§7** (not ported now). `teichmullerCharQp`'s `ringHomComp` pattern is T520's ω-as-Dirichlet-character sub-leaf verbatim. von Staudt–Clausen + B₁,ω⁻¹-pole computation become relevant at §6 (L_p(1,χ) / residue) and §7 (Kummer congruences). Convention bridge needed if porting B-lemmas: our range-sum vs their ZMod-sum (equal for nontrivial χ — T503's `hsum_eq` bijection is the bridge). |
| `LValueAtOne/` (~1900 LOC, ℂ-valued, mod p) | `odd_LFunction_zero_eq_neg_BernoulliGen_one` (L(0,χ) = −B₁,χ, odd χ mod p — the k=1 odd case of our T505); `odd/even_LFunction_one_eq_*Rhs` (L(1,χ) formulas: iπτ(χ)/p-sum for odd, τ(χ)/p·Σχ⁻¹(a)log-style for even) | **Proof-precedent for T505 and §6 planning** (not ported — ℂ-routes via sinZeta/Hurwitz functional equation; our T505 wants the direct Hurwitz-at-negative-integers route at general level N, all k). The even L(1,χ) shape is the archimedean counterpart of RJW Thm 6.2's L_p(1,χ) — consult their Even.lean decomposition when planning §6. |
| `GaussSumProduct/` (ℂ, mod p) | `(∏_{χ odd} τ(χ))² = (−p)^{|X⁻|}`, Legendre-sign, root-number pairing | Skip — h⁻-class-number-formula specific; our Gauss-sum needs (product formula at general level N) already proven in Characters.lean (T502). |
| `Reflection.lean` + stack | Kummer-pairing/Spiegelungssatz/Stickelberger/class-group machinery | Skip — Kummer's criterion infrastructure, outside RJW §5–§15 scope. |

---

# §6 pre-plan addendum (2026-06-11, /develop resume-mode scoping pass)

## Section map (read in full this session)
§6 "The values at s = 1" = TeX 1980–2180. One headline result:
**Theorem 6.1** (`s=1 theorem`, TeX 1987–1995), θ non-trivial of conductor N,
ε_N a primitive N-th root of unity:
- (i) classical: L(θ,1) = −(1/G(θ⁻¹))·Σ_{c∈(ℤ/N)ˣ} θ⁻¹(c)·log(1−ε_N^c)
  — proof §6.1 (TeX 2007–2045), Washington Thm 4.9 route: Fourier/Gauss-sum
  expansion (eq:classical 6.1) + Taylor series of −log(1−z) + convergence
  at s = 1. Parity refinement remark (TeX 2046–2053) is prose.
- (ii) p-adic (Leopoldt): L_p(θ,1) = −(1−θ(p)p⁻¹)(1/G(θ⁻¹))·Σ θ⁻¹(c)·log_p(1−ε_N^c)
  — proof §6.2 (TeX 2055–2155) via F̃_θ (the log-antiderivative of F_θ),
  Lemma 6.2 (`lem:bounded power series`: F̃_θ ∈ ℛ⁺), thm:mahler la
  (locally analytic distributions), Lemma 6.3 (`lem:mu theta'`: x·μ̃_θ = μ_θ),
  then (1−φ∘ψ)-evaluation at 0 with two cases (n ≥ 1: χ kills pℤ_p;
  n = 0: Eqphipsi ξ-sum + c ↦ pc Frobenius trick).
Closing remarks (Coleman polylogarithms Thm s=k, Perrin-Riou): PROSE-ONLY,
out of scope (record as deferred, like the §5 Mellin nodes).

## The three deferred clusters that come due (and what we actually need)

1. **Extended p-adic logarithm (Iwasawa branch)** — REQUIRED for the
   statement of (ii): the arguments 1−ε_N^c have ‖(1−ε_N^c)−1‖ = 1, outside
   padicLog's ball. Not in mathlib (surveyed). Washington §5.1 construction.
   Needed API (over the §5 ambient K): `extLog : K → K` (junk-total) with
   (a) agreement with padicLog on the ball, (b) additivity on the relevant
   multiplicative domain, (c) log of roots of unity = 0 (torsion),
   (d) log_p(x) = log_p(−x), (e) the values at 1−ε^c needed by the proof.
   Design note: for the theorem we can avoid a fully general Kˣ-log by
   defining extLog via "x^m ∈ p^k·(ball) for some m, k" (rational-valuation
   elements) with a well-definedness lemma — the arguments 1−ε_N^c qualify
   (algebraic). Generality decision to be made at decompose time.

2. **Eqphipsi / formal ψ on power series** — the deferred ξ-machinery
   (plan.md "Deferred"). §6.2's case n = 0 uses
   (φ∘ψ)F = p⁻¹·Σ_{ξ∈μ_p} F((1+T)ξ−1) literally. Two sub-pieces:
   (a) a FORMAL ψ-operator on R⟦T⟧ (the digit decomposition
   F = Σ_{i<p} (1+T)^i·φ(F_i), ψF := F_0 — ξ-free, mirrors the project's
   measure-level digit-shift ψ), with ψ∘φ = id, ψ(constants) = constants,
   compatibility with the measure-level ψ through mahlerRingEquiv;
   (b) Eqphipsi itself as a lemma (needs μ_p ⊂ K hypothesis, the §5
   hε-pattern; ∏_{ξ∈μ_p}(Yξ−1) = Y^p−1).

3. **Locally analytic distributions (ℛ⁺, thm:mahler la)** — RJW's route
   makes x⁻¹·μ_θ rigorous as a distribution. **WE CAN AVOID THIS ENTIRELY**
   (recorded route-discovery, to be adversarially tested at decompose time):
   - Our L_p(θ,1) is ALREADY a genuine measure pairing: LpFunction at s = 1
     pairs ζ_η-cleared (= x⁻¹·Res μ̃_η by construction, the §5
     zetaEtaCleared) against χ̃·⟨x⟩⁰ = χ̃. No distribution needed for the
     statement.
   - For the VALUE: let ρ := the (cleared, χ-twisted) x⁻¹Res(μ_θ)-measure
     pushed to ℤ_p (iota). Then L_p(θ,1)·(clearing) = 𝓐_ρ(0) (mass).
     ∂𝓐_ρ = 𝓐_{x·ρ} = 𝓐_{Res μ_θ} = (1−φψ)F_θ = ∂((1−φψ)F̃_θ) — wait, at the
     FORMAL level: both 𝓐_ρ and G₀ := (1−φψ)F̃_θ are ∂-antiderivatives of
     (1−φψ)F_θ, hence differ by a constant C (ker ∂ = constants).
   - **C = 0 by the ψ-kernel argument**: ρ is supported on the units, so
     ψ(𝓐_ρ) = 0 (project: isSupportedOn_units_iff_psi_eq_zero + the
     formal-ψ bridge); ψ(G₀) = ψF̃ − ψφψF̃ = 0 (ψφ = id, formal); and
     ψ(C) = C for constants. Subtract: C = 0. Hence 𝓐_ρ(0) = G₀(0) and the
     two-case computation of (φψF̃)(0) (TeX 2115–2155) finishes exactly as
     in the source — all at the level of FORMAL power series in K⟦T⟧
     (F̃_θ has unbounded coefficients but lives in K⟦T⟧; no ℛ⁺ topology,
     no distribution Mahler correspondence, no thm:mahler la).
   - F̃_θ is then just an EXPLICIT power series (constant term
     Σθ⁻¹(c)·extLog(ε^c−1)-shaped, higher coefficients the log-expansion of
     TeX 2076–2080), with ∂F̃_θ = F_θ a finite per-c formal-derivative
     computation + Σ_c θ⁻¹(c) = 0.
   This replaces RJW's §3.7-dependent argument with a replan-note-eligible
   Lean-friendlier route; the SOURCE's statements (Lem 6.2/6.3) become:
   Lem 6.2 → the explicit coefficient formula for F̃_θ (its ℛ⁺-membership is
   not needed and is recorded as deferred prose); Lem 6.3 → the ∂F̃ = F_θ
   identity + the ψ-kernel constant-pin (the "x·μ̃ = μ" content at the level
   we use it). Faithfulness: statement of Thm 6.1(ii) UNCHANGED; the route
   is a recorded replan (rule 5 pattern, cf. T018/T026/L5.3.3).

## Mathlib survey status (1c, partial — full survey at decompose time)
- Complex Dirichlet L: mathlib has LSeries/Dirichlet + DirichletContinuation
  (functional equation `IsPrimitive.completedLFunction_one_sub`),
  HurwitzZetaValues, ZMod.LFunction. The exact log(1−ε^c)-formula at s = 1
  is NOT obviously present — expect to build it from `LSeries` of the
  twisted-coefficient function + Taylor/Abel summation; survey area B
  (special values) must be COMPLETED at decompose time (it never ran).
- Locally analytic distributions / Amice: absent (grep clean) — moot if the
  distribution-free route survives the adversarial pass.
- Extended/Iwasawa log: absent.
- μ_p-products (∏(Yξ−1) = Y^p−1 etc.): standard `X_pow_sub_one_eq_prod`
  machinery present (RootsOfUnity).

## Proposed cluster structure (sizing vs TeX line counts; ticket-grade
decomposition to be produced by the Phase-1e pass)
- W6a extLog cluster (~5–7 leaves; Washington §5.1 ~1 page) — independent.
- W6b formal-ψ/digit + Eqphipsi cluster (~4–6 leaves; the §3 deferral) —
  independent.
- C6 complex value (i) (~4–6 leaves; TeX 2007–2045 ≈ 39 lines + mathlib
  LSeries glue) — independent of W6a/W6b.
- P6 p-adic value (ii) (~6–9 leaves; TeX 2055–2155 ≈ 100 lines): F̃_θ def +
  ∂F̃ = F_θ + ψ-kernel pin + the two-case (φψF̃)(0) + assembly into
  LpFunction-at-1. Depends on W6a, W6b, §5 stack.
- Blueprint: new §6 chapter nodes (Thm 6.1 (i)/(ii), Lem 6.2/6.3 with the
  replan prose notes, Coleman/PR remarks as unwired prose).

## Open scope questions for the user (pre-decompose)
1. Approve the distribution-free route for (ii) (recorded replan; ℛ⁺/§3.7
   stays deferred until the notes force it — likely §8 Eisenstein family /
   later Coleman-map sections)?
2. extLog generality: pragmatic rational-valuation domain (enough for
   Thm 6.1) vs full Iwasawa log on Kˣ (more work, PR-shaped)?
3. Complex side (i): formalise against mathlib's LFunction (preferred,
   mathlib-linking directive) — accept that the bridge LSeries↔our LvalNeg
   conventions may add a leaf or two?

---

# §7 pre-plan addendum (2026-06-12, /develop pass)

## Section map (read in full this session)
§7 "The residue of ζ_p at s = 1" = TeX 2181–2360. One headline:
**Theorem 7.1** (`thm:residue`, TeX 2187–2194): (i) ζ_{p,i} analytic at
s = 1 for i ≠ p−1; (ii) ζ_{p,p−1} has a simple pole at s = 1 with residue
1 − p⁻¹. Proof: Eqtmp2 (TeX 2199–2215) writes ζ_{p,i}(s) as the
pseudo-measure quotient with denominator g_{a,i}(s) = ω(a)^i⟨a⟩^{1−s} − 1
— EXACTLY our `zetaPBranch` definition (T519), so Eqtmp2 is definitional
for us. Lemma 7.2 (`lem:g p-1`): g-vanishing analysis + the limit
(s−1)⁻¹g_{a,p−1}(s) → −log_p(a). Then eq:zeta-p-residue reduces (ii) to
the mass ∫x⁻¹μ_a = ((1−φψ)F̃_a)(0) with F̃_a := log(T/(1+T)·(1+T)^a/((1+T)^a−1))
(Lemmas 7.3–7.5, TeX 2266–2352): ∂F̃_a = F_a, ℛ⁺-membership (Lemma 7.4 —
SKIPPED by our distribution-free route, as Lem 6.2 was), and the
φψ-evaluation via the Eqphipsi ξ-sum with {ξ^a} = μ_p and
∏(Xξ−1) = X^p−1, giving ((1−φψ)F̃_a)(0) = −(1−p⁻¹)log_p(a).

## Key reuse (the §5/§6 investment pays)
- "analytic/pole/limit" statements: topological limits in ℤ_p-variable;
  (ii) as `Tendsto (fun s => (s−1)·zetaPBranch p hp2 (p−1) s) (𝓝[≠] 1)
  (𝓝 (1−p⁻¹))` — K-FREE final statement (the log_p(a)'s cancel).
- Lemma 7.2's limit: through the T523 exp/log bridge —
  ⟨a⟩^{1−s} − 1 = pZpExp((1−s)·pZpLog⟨a⟩) − 1, then the exp-derivative-at-0
  (‖exp w − 1 − w‖ ≤ p‖w‖², new small lemma) + ‖exp w − 1‖ = ‖w‖. Also
  yields the Lipschitz bound ‖y^t − 1‖ = ‖t‖·‖y − 1‖ (p odd) powering the
  continuity of s ↦ zetaPBranch (Thm (i)).
- The mass computation: the c₀-design VERBATIM (T615-pattern):
  ρ_a := baseChange of the §4 numerator measure (zetaNum p a is already
  x⁻¹·Res(μ_a) on units!), ψρ_a = 0, ∂𝓐ρ_a = (1−φψ)F_a-series, the
  antiderivative/ker-∂ pin, ξ-point evaluation via sum_seriesEval_mahlerK.
- F̃_a explicit: F̃_a = [−extLog(a) + log(1+T·h)-series] + (a−1)•formalLog
  with the §4 PropFaT-style h-series; a := the ℕ-generator
  (exists_nat_topological_generator) so all binomials are integral.
- ξ-field: the machinery needs μ_p ⊂ K; final statements are ℚ_p-level —
  compute in K and descend by injectivity. K := ℂ_[p] (mathlib
  `PadicComplex`: NormedField/IsUltrametricDist/CharZero instances exist;
  CompleteSpace from completion; NormedAlgebra ℚ_[p] — verify at
  execution; primitive p-th root from PadicAlgCl mapped in). SURVEY-GATED
  leaf; fallback: SplittingField + spectralNorm instances.

## New file: PadicLFunctions/ResidueZeta.lean (imports Branches +
ValuesAtOne); generic exp-facts may migrate to PadicExp.lean at a later
cleanup (placement note).

## Open risks
- ℂ_[p]-instance pack completeness (NormedAlgebra ℚ_[p] ℂ_[p] +
  CompleteSpace + the root) — survey-gated T707a.
- The §4 PadicMeasure-units ↔ MeasureR-K bridge for zetaNum (baseChange is
  on ℤ_p-measures; compose with the Measure-level iota).
- {ξ^a} = μ_p needs gcd(a,p) = 1 — the §4 generator a is coprime to p
  (topological generator of ℤ_p^× reduces to a generator mod p; extract
  from the T037 machinery).

## §7 COMPLETE (2026-06-12, /beastmode)
All of T701–T708 + 3 cleanups done in one session; project-wide ZERO
sorries, axioms standard, blueprint Residue chapter wired + site rendered.
Risk outcomes: ℂ_[p]-pack complete in mathlib (no fallback needed; ξ via
`HasEnoughRootsOfUnity.exists_primitiveRoot`); the zetaNum bridge ran
through ℤ_p-level cmul + `baseChange_cmul`/`baseChange_res` (no new
naturality lemma); the {ξ^a}-reindex was replaced by a product collapse
(Finset.prod_nbij' over ZMod p + Fermat + `extLog_eq_of_witness`), avoiding
ExtLogDomain(ξ^i−1) entirely. Statement fixes (b2-logged, T704): ∂F̃_a = F_a
needs ¬p∣a (Fa junk at p∣a); constantCoeff_FtildeA needs a ≠ 0. New
reusable infrastructure: the K-level seriesEval∘subst bridge
(`seriesEval_subst_formalLog`) — FormalPsi-placement candidate
(CLEANUP-FINAL). Next: §8 (Iwasawa's theorem / μ-invariant chapters per
the blueprint roadmap) or the deferred D = 1 case of Thm 6.1(ii).

# §8 pre-plan addendum (2026-06-12, /develop pass)

## Section map (read in full this session)
§8 "The p-adic family of Eisenstein series" = TeX 2361–2446, the Part-I
closer. One Definition (p-stabilisation E_k^{(p)} := E_k − p^{k−1}E_k(p·),
TeX 2387), one impossibility gloss (no measure interpolates k ↦ p^k,
TeX 2379–2383), one Theorem (TeX 2399–2416): the Λ-adic family
𝐄 = Σ A_n qⁿ ∈ Q(ℤ_p^×)⟦q⟧ with A₀ = xζ_p/2, A_n = Σ_{d∣n, p∤d} δ_d, and
∫x^{k−1}·𝐄 = E_k^{(p)} coefficientwise for even k ≥ 4. The notes' proof is
8 lines: §4's interpolation does all the work.

## Key facts and reuse
- Convolution ring Λ(ℤ_p^×) = `PadicMeasure p ℤ_[p]ˣ` (CommRing instance,
  PseudoMeasure.lean), `QuotientField`, `IsPseudoMeasure`, `padicZeta`,
  `padicZeta_moments` (witness-encoded), `dirac_sub_one_mem_nonZeroDivisors`,
  the zero-divisor lemma `eq_zero_of_forall_unitsPowCM_eq_zero`, and
  `units_mul_apply_unitsPowCM` ((μ*ν)(x^k) = μ(x^k)ν(x^k)) — everything
  the family needs is §3.6/§4 infrastructure.
- The x-twist τ = unitsCmul (unitsPowCM 1) is a ring automorphism by a
  pure moments check (decomposition R8.2) — no new analysis.
- **Erratum #11 (errata.md)**: TeX 2403's "(a) A₀ is a pseudo-measure" is
  false with Def 3.34 — the pole of xζ_p is at the character x⁻¹.
  Formalised in the corrected twisted form (g[g]−[1])·A₀ ∈ Λ (replan R8.1).
- Complex side: mathlib HAS the level-1 Eisenstein q-expansion
  (`EisensteinSeries.E`, `E_qExpansion_coeff`, `q_expansion_bernoulli` —
  Mathlib/NumberTheory/ModularForms/EisensteinSeries/QExpansion.lean) with
  the constant-1 normalisation; RJW's E_k = (ζ(1−k)/2)·E. Stabilised
  q-expansion proved as a HasSum statement (replan R8.3); the
  σ^p-arithmetic σ^p_{k−1}(n) = σ_{k−1}(n) − p^{k−1}σ_{k−1}(n/p) is a
  divisor-sum reindex against mathlib's `ArithmeticFunction.sigma`.
- Impossibility (TeX 2379) via uniform Euler congruence x^{φ(p^{n+1})} ≡ 1
  mod p^{n+1} (the §7 unitsToZModPow/ker_toZModPow patterns) +
  `norm_apply_le`.

## Files
- `PadicLFunctions/EisensteinFamily.lean` — p-adic side (imports ZetaP;
  light). Twist, A_n, A₀, family, milestone theorem, impossibility.
- `PadicLFunctions/EisensteinComplex.lean` — complex side (imports mathlib
  EisensteinSeries.QExpansion + our ZetaValuesComplex; heavy mathlib
  imports kept out of the p-adic file). σ^p arithmetic + stabilised HasSum.

## Deferred (§8)
- ~~**Γ₀(p)-modularity of E_k^{(p)}**~~ — **UN-DEFERRED 2026-06-12** (user
  directive): the strong-multiplicity-one project
  (CBirkbeck/LeanModularForms, branch hecke-ring) supplies the
  level-raising operator `modularFormLevelRaise` (Miyake §4.6 Lem 4.6.1);
  the repo now requires it (lakefile.toml pin 720d950b + two
  mathlib-skew compat fixes, to be upstreamed at CLEANUP-82). Ticket T808.
- Remarks 1–3 (TeX 2431–2446: Λ-adic forms colloquium, weight space 𝒲,
  Hida/Coleman families) — prose only, no mathematical content to
  formalise; blueprint prose covers them.

## Generality
ℤ_p-coefficients throughout (standing rule 6); the family lives over
`QuotientField p` exactly as the source's Q(ℤ_p^×)⟦q⟧. p = 2 excluded
where ζ_p enters (hp2 standing); the Dirac/divisor-measure layer and the
impossibility lemma are p-general.

## §8 COMPLETE (2026-06-12, /beastmode) — PART I COMPLETE
All of T801–T808 + 3 cleanups done in one session; project-wide ZERO
sorries, axioms standard, blueprint Eisenstein chapter wired + site
rendered. The Λ-adic family theorem (`eisensteinFamily_interpolation`) is
the milestone; the erratum-#11-corrected A₀-claims
(`twistedZetaHalf_isTwistedPseudoMeasure`/`_moments`) carry the notes'
"(a)"; the q-expansion (`hasSum_stabilisedEisenstein`) and the
Γ₀(p)-modularity (`stabilisedEisenstein`, via the un-deferral) carry the
complex side. New external dependency: CBirkbeck/LeanModularForms at
branch compat/padic-mathlib-431 (= hecke-ring 720d950 + 4 mechanical
mathlib-skew fixes, pushed upstream 84b03fb) supplying the level-raising
operator. With §§3–8 done, Part I of RJW is fully formalised. Next:
Part II (§§9–11: the Coleman map, Iwasawa's theorem, the Main
Conjecture — blueprint chapters exist) or the deferred D = 1 case of
Thm 6.1(ii), or CLEANUP-FINAL in a tooled session.

# §9–§10 pre-plan addendum (2026-06-12, /develop pass) — PART II OPENS

## Section map
§9 (TeX 2466–2511): Part-II notation — only the LOCAL tower
(K_n = ℚ_p(μ_{p^n}), 𝒰_n, π_n, norm-limits 𝒰_∞) is §10-load-bearing;
global/Galois objects ride the §11 pass. §10 (TeX 2512–2948): Coleman's
theorem (𝒰_∞ ≅ (ℤ_p⟦T⟧^×)^{𝒩=id}, u ↦ f_u with f_u(π_n) = u_n), the
cyclotomic units c(a) with f_{c(a)} = ((1+T)^a−1)/T and
∂log f_{c(a)} = a−1−F_a, the Coleman map Col, and
**ζ_p = Col(c(a))/θ_a** (thm:coleman to kl) — the arithmetic
reconstruction of the Kubota–Leopoldt pseudo-measure. §10.5
(Euler systems/Perrin-Riou): prose-only, deferred.

## Design (decomposition R10.1–R10.8)
The tower lives inside ℂ_[p] (PadicComplex — the §7/§8 investment):
fixed compatible ξ-system by recursion + IsAlgClosed; K n :=
ℚ_p⟮ξ n⟯ IntermediateField; O n := norm-unit-ball; degree ladder by
Eisenstein (Φ_{p^n}(T+1) Eisenstein at p over ℤ_[p]); evaluation
f(π_n) := our seriesEval (§6–§8 layer; mathlib's new
PowerSeries.eval₂ as fallback); 𝒩 := φ⁻¹∘(det in the PROVEN digit
basis (1+T)^i of ℤ_p⟦T⟧ over φ(ℤ_p⟦T⟧)) — no field-norm theory, no
illegal μ_p-substitution (the Eqphipsi subtlety); commuting square by
RingHom.map_det; compactness of ℤ_p⟦T⟧^× by Pi-topology + Tychonoff +
metrizability; uniqueness by mathlib's NEW Weierstrass preparation.

## Files
- `PadicLFunctions/Coleman/Tower.lean` — ξ-system, K/O/π/𝒰, degree
  ladder, element norms (X^p−ξ_n collapse), 𝒰_∞.
- `PadicLFunctions/Coleman/NormOperator.lean` — digit-basis algebra,
  𝒩, ψ-trace relation, continuity lemmas, compactness.
- `PadicLFunctions/Coleman/Theorem.lean` — eval-at-π_n, single-level
  lemma, Weierstrass uniqueness, commuting square, R, surjectivity,
  Coleman's theorem (both forms).
- `PadicLFunctions/Coleman/Map.lean` — cyclotomic units, ∂log-bridge
  to F_a, Col, thm:coleman to kl.

## Deferred (§9–§10)
- §10.5 Kummer/Euler systems/Perrin-Riou (TeX 2847–2948): prose-only
  in source ("may be skipped"); blueprint ColemanMap chapter prose
  covers it; no Lean.
- §9's global tower (F_n, 𝒱_n), +-subfields, 𝒢 ≅ ℤ_p^×: §11 pass.
- 𝒰_{n,1}-structure (ℤ_p-module): §11 pass (not §10-load-bearing).

## Standing deferred queue (status 2026-06-12)
- D = 1 case of Thm 6.1(ii): queued as board ticket T-D61 (a
  /develop --decompose planning ticket — the notes' own gap, errata #6;
  the §8 twist machinery is the expected key).
- CLEANUP-FINAL: still blocked on a lean-lsp-MCP-tooled session.
- LeanModularForms compat branch: tidied + repinned (bc83277) — CLOSED.

# §11 pre-plan addendum (2026-06-12, /develop pass)

## Section map (read in full this session)
§11 "Iwasawa's theorem on the zeros of the p-adic zeta function" =
TeX 2949–3112 (`sec:iwasawa zeros`), three subsections:
- **11.1 Measures on Galois groups** (2964–3042): the identification
  Λ(𝒢) = Λ(ℤ_p^×) via the cyclotomic character (the notes' own move,
  TeX 2970: "From now on, we will let Λ(𝒢) be the space of measures on
  𝒢, which we identify with Λ(ℤ_p^×)"); the ±-decomposition
  M ≅ M⁺ ⊕ M⁻ via the idempotents (1±c)/2 (lem:decompose plus minus,
  p odd); Λ(𝒢)⁺ ≅ Λ(𝒢⁺) where 𝒢⁺ ↔ ℤ_p^×/{±1}; the odd-moment
  criterion for Λ(𝒢⁺)-membership; **corollary: ζ_p is a pseudo-measure
  on 𝒢⁺** (its interpolated odd moments vanish — k = 1 via the Euler
  factor 1−p⁰, odd k ≥ 3 via B_k = 0; the notes' proof line "ζ(1−k)=0
  for odd k ≥ 1" is wrong at k = 1: **erratum #13**).
- **11.2 The ideal generated by ζ_p** (3043–3059): I(𝒢)ζ_p and
  I(𝒢⁺)ζ_p are ideals (pseudo-measure property + the augmentation
  ideal's description by [g]−[1]'s — for us: the already-proven
  principality `augmentationIdeal_eq_span`).
- **11.3 Cyclotomic units and Iwasawa's theorem** (3060–3112): the
  global cyclotomic units 𝒟_n = 𝒪_{F_n}^× ∩ ⟨±ξ, ξ^a−1⟩ and 𝒟_n⁺; the
  class-number theorem [𝒱_n : 𝒟_n] = h_n⁺ (**stated, not proven** —
  cites Washington Thm 8.2; stays deferred prose); the local closures
  𝒞_n, 𝒞_{n,1}, 𝒞_{∞,1} (+ plus variants); **thm:iwasawa**
  (𝒰⁺_{∞,1}/𝒞⁺_{∞,1} ≅ Λ(𝒢⁺)/I(𝒢⁺)ζ_p, proof in §12 = TeX
  3113–3616). Plus the §9-deferred notation now due: 𝒰_n, 𝒰_{n,1}
  (with its ℤ_p-power structure, TeX 2494–2496), 𝒰_{∞,1}, F_n, 𝒱_n,
  ⁺-subfields (TeX 2470–2505).

## Scope decision (per-section discipline)
The §11 board formalises §11's own proven content + its definitions.
**thm:iwasawa is NOT stated in Lean this board**: its statement needs
the Λ(𝒢⁺)-module structures on 𝒰⁺_{∞,1}/𝒞⁺_{∞,1} and the induced
Coleman map, which the notes construct only in §12.1–12.2 ("We will
see that…", TeX 3096) — a sorry-free board cannot state it without
swallowing §12's constructions. It lands with its proof on the §12
board. Likewise thm:cyclo-units-class-number is permanently
deferred prose (the notes themselves do not prove it).

## Key reuse (everything is already on the shelf)
- `deg`/`augmentationIdeal`/`augmentationIdeal_eq_span` (principality
  for a topological generator!), `exists_topological_generator`,
  `dirac_sub_one_mem_nonZeroDivisors`, `eq_zero_of_forall_unitsPowCM_eq_zero`,
  `units_mul_apply_unitsPowCM`, `pseudoMeasure_eq_zero_of_moments`,
  `IsPseudoMeasure`, `padicZeta`, `padicZeta_moments` (witness-encoded),
  `isUnit_two_padicInt` — PseudoMeasure.lean + ZetaP.lean +
  EisensteinFamily.lean.
- `integral_swap`/`innerInt` are ALREADY general over compact spaces —
  the convolution ring generalises to any compact commutative
  topological monoid with zero new analysis (T1101).
- Coleman layer: `K`/`O`/`pi`/`levelNorm`/`NormCompatUnits` (One/Mul
  only — group-ification is a §11 ticket), `cycloUnit`/`cyclo` with
  `cycloUnit_mem_O`/`inv_cycloUnit_mem_O` — Tower.lean + Map.lean.
- mathlib: `QuotientGroup` topology pack (CompactSpace G⧸N instance,
  `instIsTopologicalGroup`, `isQuotientMap_mk`, `isOpenQuotientMap_mk`),
  `bernoulli_eq_zero_of_odd`, `addChar_of_value_at_one` (ℤ_p-powers of
  1-units in complete ultrametric ℤ_[p]-algebras),
  `LinearAlgebra/Projection` idempotent API. NO involution
  eigen-splitting in mathlib (A1 is a project lemma, PR candidate).

## §11 design decisions
1. **Galois side = identified side** (replan R11.1): all §11 measure
   results are formalised on Λ(ℤ_p^×) with c := (−1 : ℤ_[p]ˣ), per the
   notes' own identification (TeX 2970). 𝒢⁺ := ℤ_[p]ˣ ⧸ zpowers(−1)
   (quotient topological group). The genuine Galois objects move down
   the deferral queue: finite-level LOCAL Gal(K_n/ℚ_p) ≅ (ℤ/p^n)^× to
   §12 (equivariance forces it); the infinite/global 𝒢 = Gal(F_∞/ℚ)
   only when §13 forces it.
2. **Convolution algebra generalised in place** (T1101, replan R11.5):
   PseudoMeasure.lean's hardcoded `CommRing (PadicMeasure p ℤ_[p]ˣ)`
   becomes `CommRing (PadicMeasure p G)` for `[CommMonoid G]
   [ContinuousMul G] [CompactSpace G]` — RJW Rem 3.33's own generality;
   `deg`/`augmentationIdeal` generalise with it. Statement-preserving
   contract: all downstream names (`units_mul_apply`, …) keep their
   exact statements (abbrev/restatement), full `lake build` gates.
3. **Λ(𝒢)⁺ ≅ Λ(𝒢⁺) by the functional even-part route** (replan
   R11.2): π_* := pushforward along mk is a ring hom; the section
   ν ↦ ν ∘ (descend ∘ evenPart) inverts it on the plus part. The
   source's finite-level rank count would require the Prop 3.9/3.10
   projlim presentation — **which stays deferred** (now pointed at
   §12, where Λ(𝒢)-module structures on projlim 𝒰_{n,1} first make it
   load-bearing; §11 needs none of it).
4. **Pseudo-measure on 𝒢⁺ without a 𝒢⁺-moment theory**: regularity of
   [ā]−1 in Λ(𝒢⁺) and the principality of I(𝒢⁺) transport through the
   section + ker π_* = Λ⁻ = ([−1]−1)Λ; no Mahler/levelMap theory on
   the quotient. ζ_p⁺ := π_*(ν_a)/([ā]−1); well-definedness of pushed
   witnesses = the c-invariance ([−1]−[1])ζ_p = 0 (the corollary's
   real content).
5. **I(𝒢)ζ_p as a carrier-defined Ideal** with `eq_span`
   characterisation (replan R11.4): the notes' "topological ideal
   generated by [g]−[1]" is replaced by the stronger already-proven
   principality.
6. **Unit towers stay inside ℂ_[p]** (R10.1 continuation, replan
   R11.7): 𝒰_n := units-of-O_n as a Subgroup ℂ_[p]ˣ; 𝒰_{n,1} via
   ‖u−1‖ < 1 (= "≡ 1 mod 𝔭_n"); ℤ_p-powers via
   `addChar_of_value_at_one`; F_n := ℚ⟮ξ_n⟯, F_n⁺ := ℚ⟮ξ+ξ⁻¹⟯ as
   IntermediateField ℚ ℂ_[p]; 𝒱_n := units integral over ℤ (with
   integral inverse); 𝒟_n := ⟨±ξ, ξ^a−1⟩ ⊓ 𝒱_n; 𝒞_n :=
   topologicalClosure(𝒟_n) ⊓ 𝒰_n; 𝒞_{∞,1} etc. as subgroups of the
   group-ified NormCompatUnits. Milestone: c(a) ∈ 𝒟_n / 𝒞_{∞,1}
   (TeX 3084's sentence — the Coleman input is a global cyclotomic
   unit).
7. p odd (hp2) wherever the ±-splitting or ζ_p enters (the section
   assumes it, TeX 3004); the bare c-invariance criterion (C2) is
   p-general and stated so.

## Files (new directory PadicLFunctions/Iwasawa/)
- `Iwasawa/PlusPart.lean` — involution splitting (general), c-action
  on Λ, plus/minus parts, 𝒢⁺, π_*, even-part section, the iso, kernel.
- `Iwasawa/ZetaGalois.lean` — odd moments, c-invariance, ζ_p⁺,
  pseudo-measure on 𝒢⁺, I(𝒢⁺) principality, zetaIdeal(Plus).
- `Iwasawa/LocalUnits.lean` — 𝒰_n/𝒰_{n,1}(⁺), ℤ_p-powers,
  NormCompatUnits group-ification, 𝒰_{∞,1}(⁺).
- `Iwasawa/CyclotomicUnits.lean` — F_n/F_n⁺/𝒱_n/𝒟_n(⁺)/𝒞-towers,
  norm-of-integral lemma, c(a)-membership milestone.
- Refactor in place: `Measure/PseudoMeasure.lean` (T1101).

## Deferred (§11 update)
- Props 3.9/3.10 (projlim presentation): deferral pointer moves
  §11 → §12 (first load-bearing for Λ(𝒢)-module structure on
  𝒰_{∞,1}; §11 proven functionally without it).
- Local finite Galois Gal(K_n/ℚ_p) ≅ (ℤ/p^n)^×: → §12 (equivariance).
- Global/infinite 𝒢 = Gal(F_∞/ℚ) ≅ ℤ_p^× (Krull): → §13 (or never, if
  the identified side continues to carry the mathematics; blueprint
  prose notes the identification).
- thm:cyclo-units-class-number (TeX 3072): permanently deferred prose
  (Washington Thm 8.2 — the notes don't prove it; blueprint node stays
  unwired).
  **flt-regular-bernoulli survey (user directive 2026-06-13)**: the user's
  repo (`~/Documents/GitHub/flt-regular-bernoulli`,
  `BernoulliRegular/CyclotomicUnits/` + `FLT37/…/Sinnott/` +
  `TotallyRealSubfield/`) has a substantial cyclotomic-unit index
  development since the §5 survey: `realCyclotomicUnit` in `(𝓞 K⁺)ˣ`
  (mathlib `NumberField.maximalRealSubfield`, `IsCMField`),
  `hPlus K := card (ClassGroup (𝓞 K⁺))`, `cyclotomicUnitIndexSubgroup`,
  and the p-primary index theorems
  `cyclotomicUnitIndex_primeConductor_pPrimary_of_{sinnottIndexFormula,
  kummerDirichletDeterminant}` : `p ∣ index ↔ p ∣ h⁺`. LIMITS: prime
  conductor only (K = ℚ(ζ_p), not the tower ℚ(μ_{p^n})); p-primary
  divisibility only (not the exact index h_n⁺ = [𝒱_n : 𝒟_n]);
  CONDITIONAL on named unproven analytic cores
  (`FLT37.Sinnott.SinnottIndexFormula` is a Prop-valued hypothesis with
  no provider theorem in the repo; some files carry sorries); abstract
  NumberField setting vs our inside-ℂ_p towers. VERDICT: not a discharge
  of RJW Q9 (which stays deferred prose), but the p-primary
  `p ∤ index ↔ p ∤ h⁺` form is EXACTLY the Vandiver-shaped input of
  §13's Main-Conjecture-for-Vandiver-primes proof (TeX 3753) — record as
  a candidate external dependency for the §13 pass (the LeanModularForms
  precedent), to be re-assessed (incl. whether its analytic core is
  discharged by then) when §13 is planned.
- thm:iwasawa statement + proof: §12 board.
- Rem 3.7/3.8 clopen-additive-functions equivalence: still unused;
  keep deferred.

## §§9–10 COMPLETE (2026-06-12, /beastmode)
T901–T912 (+ the spawned T903b/T904b) and all cleanups done in one
session; project-wide ZERO sorries, axioms standard, blueprint ColemanMap
chapter fully wired (17 nodes) + site rendered. **Coleman's theorem**
(`coleman_existsUnique`/`colemanSeries`, the diagonal through the
compactness extraction) and **ζ_p = −Col(c(a))/θ_a** (`coleman_to_kl` —
the honest sign; **erratum #12**: the notes' display at TeX 2839 drops
the minus their own lemma at 2614 carries). Design outcomes: the tower
inside ℂ_p paid off everywhere (seriesEval evaluation, the spectral-norm
bridge only at T903b); 𝒩 via the digit-basis determinant avoided all
field-norm/μ_p-product theory (T907 det-transport; T908(ii) via
Frobenius-over-𝔽_p; (iii) via `Matrix.det_one_add_smul` + the trace
identity tr(digitMatrix h) = p·ψ(h) — RJW TeX 2670 realised); Eisenstein
gave the degree ladder; T903b's orthogonality/value-group joint induction
replaced monogenicity-by-discriminants. Deferred-debt: the D61 sub-board
(D611–D613, Route A: χ against ζ_p-witnesses) is written and GATED on its
own 1i review. Next: §11 (Iwasawa's theorem on the zeros, TeX 2949+) or
release the D61 gate, or CLEANUP-FINAL in a tooled session.

## §11 statement-fix note (2026-06-13, b2-logged at T1113)
The board's milestone packaging claimed cyclo ∈ 𝒞_{∞,1} unconditionally;
the principal-unit membership needs a ≡ 1 (mod p) (c_n(a) ≡ a mod 𝔭_n).
Fixed minimally (hypothesis added to the three affected lemmas; 𝒟_n-
membership stays unconditional = RJW TeX 3084's literal claim). **§12
handoff**: a topological generator is never ≡ 1 mod p (p > 3), so the
coleman_to_kl generator's tower is NOT itself in 𝒞_{∞,1}; §12's
lem:closure / fundamental-exact-sequence layer performs the principal-
unit normalisation — thread this through the §12 /develop pass.

# §12 pre-plan addendum (2026-06-13, /develop pass) — the proof of Iwasawa's theorem

## Section map (read in full this session: TeX 3113–3616)
§12 "Proof of Iwasawa's theorem" (`sec:proof Iwasawa`) proves thm:iwasawa
(stated, unwired, in §11). Five subsections:
- **12.1 Equivariance of the Coleman map** (3117–3249): equip 𝒰_{∞,1} with
  a Λ(𝒢)-module structure (compatible ℤ_p- and 𝒢-actions) and show Col is
  Λ(𝒢)-equivariant. ℤ_p-action: Col restricts ℤ_p-equivariantly to 𝒰_{∞,1}
  (key: a₀(u) ≡ 1 mod p ⟹ f_u−1 ∈ (p,T) ⟹ f_u^a converges = f_{u^a};
  ∂log(f_u^a) = a·∂log f_u). 𝒰_∞ = μ_{p−1} × 𝒰_{∞,1} (split SES from
  reduction mod 𝔭_n); μ_{p−1} killed by Col (constants killed by ∂log).
  𝒢-action: σ_a(f)(T) = f((1+T)^a−1); Col 𝒢-equivariant (map-by-map:
  ∂log(σ_a f)=a·σ_a ∂log f; ∂⁻¹∘σ_a = a⁻¹ σ_a∘∂⁻¹). cor:G-eq.
- **12.2 The fundamental exact sequence** (3261–3441): thm:log der (the CCW
  short exact sequence 0→μ_{p−1}→(ℤ_p⟦T⟧^×)^{𝒩=id} →[Δ] ℤ_p⟦T⟧^{ψ=id}→0)
  + lem:rest zp* (0→ℤ_p→ℤ_p⟦T⟧^{ψ=id} →[1−φ] ℤ_p⟦T⟧^{ψ=0}→ℤ_p→0) +
  def:Zp(1) + thm:fund exact seq (0→μ_{p−1}×ℤ_p(1)→𝒰_∞ →[Col] Λ(𝒢)→ℤ_p(1)→0,
  restricting to 0→ℤ_p(1)→𝒰_{∞,1}→Λ(𝒢)→ℤ_p(1)→0 as Λ(𝒢)-modules).
- **12.3 Generators for global cyclotomic units** (3450–3492): γ_{n,a} =
  ξ^{(1−a)/2}c_n(a) ∈ 𝒟_n^+; lem:cyc units gen (𝒟_n^+ gen by −1 and the
  γ_{n,a}; 𝒟_n gen by ξ and 𝒟_n^+); cor:cyc units gen 2 (if a generates
  (ℤ/p^n)^× then γ_{n,a} generates 𝒟_n^+ as a ℤ[𝒢_n^+]-module).
- **12.4 Generators for local cyclotomic units** (3495–3578): lem:closure
  (p-adic closure of ⟨g_i⟩_ℤ = ℤ_p-span, for g_i ∈ 𝒰_{n,1}); lem:global
  generators 2 (wγ_{n,a} ∈ 𝒰_{n,1}, (wγ_{n,a})^{p−1} generates (p−1)𝒟_n^+);
  LemmaGeneratorCinfty1 (𝒞_{n,1}^+ cyclic ℤ_p[𝒢_n^+]-mod gen by wγ_{n,a};
  𝒞_{∞,1}^+ cyclic Λ(𝒢^+)-mod gen by (wγ_{n,a})_n).
- **12.5 End of the proof** (3582–3608): thm:iwasawa 2 — (i) SES
  0→𝒰_{∞,1}/𝒞_{∞,1}→Λ(𝒢)/I(𝒢)ζ_p→ℤ_p(1)→0; (ii) iso
  𝒰_{∞,1}^+/𝒞_{∞,1}^+ ≅ Λ(𝒢^+)/I(𝒢^+)ζ_p (the (i)-cokernel ℤ_p(1) dies on
  the +-part since c acts by −1 and p is odd).

## Substrate (survey 2026-06-13) — §12 rests on §3–§11
PRESENT and load-bearing: φ/ψ on measures AND series (`phiHom`, `phiSeries`,
`psiSeries_phi_padicInt` = ψφ=id, `psi`/`phi`/`res_units_eq` = 1−φψ on
measures); `del` = ∂, `dlog`, `dlog_geomSum`; `normOp` 𝒩 + `ModEqPow` +
`phi_injective_mod` + `digitBasis` + ℤ_p⟦T⟧^× compactness; `colemanSeries`/
`coleman_existsUnique`/`Col`/`Col_cyclo`/`coleman_to_kl`; `NormCompatUnits` +
`levelNorm` + `zpPow` + `localUnitsOneModule` (the ℤ_p-action on 𝒰_{n,1}!) +
`unitsTower1`/`cycloTower1`/`cycloUnits`/`globalUnits`/`cyclo`; the §11
Λ(𝒢)/Λ(𝒢⁺) layer (`cAct`/`plusPart`/`minusPart`/`GPlus`/`projPlus`/`plusEquiv`/
`isCompl_plusPart_minusPart`/`padicZetaPlus`/`zetaIdeal`/`zetaIdealPlus`); the
Mahler ring-iso `mahlerRingEquiv`.

## The two large NEW sub-developments (the critical path)
1. **The Galois action on the tower (E12.1) — ABSENT, the linchpin.** Every
   Λ(𝒢)-equivariance statement rests on a 𝒢-action on 𝒰_∞ by σ_a(ξ_n) =
   ξ_n^{a mod p^n}. mathlib supplies the ABSTRACT iso
   `IsCyclotomicExtension.autEquivPow : (K_n ≃ₐ[ℚ_p] K_n) ≃* (ZMod (p^n))ˣ`
   and `IsPrimitiveRoot.autToPow`/`modularCyclotomicCharacter` (σ ↦ the a with
   σζ = ζ^a) — and Tower.lean ALREADY has `isCyclotomicExtension_K`
   ({p^n} ℚ_[p] (K p n)), so `autEquivPow` is available per level. The NEW work
   is realising the action ON OUR CONCRETE ℂ_p-TOWER, compatibly: (a) for
   a : ℤ_[p]ˣ and n, the automorphism τ_{a,n} := (autEquivPow …).symm
   (unitsToZModPow a) of K_n; (b) tower-compatibility τ_{a,n+1}|_{K_n} = τ_{a,n}
   (so they assemble to an action on 𝒰_∞ = NormCompatUnits); (c) commutation
   with levelNorm (Galois-equivariance of the field norm — mathlib
   `Algebra.norm_eq…`/conjugation invariance); (d) σ_a(ξ_n) = ξ_n^{a_n} (the
   autToPow_spec). The action on power series σ_a(f) = f((1+T)^a−1) and the
   compatibility f_{σ_a u} = σ_a f_u (interpolation + uniqueness) close the
   equivariance of the first Coleman-map factor. SIZING: this is its own
   cluster, ~6–9 leaves, the gating sub-project (a 1–2 page argument in the
   source spread over 3184–3243 but heavy in our concrete model). Generality
   note: the action is most naturally `MulDistribMulAction (𝒢_n) (𝒰_n)` /
   a `ℤ_[p]ˣ`-action on NormCompatUnits; design at decompose time.
2. **thm:log der — the CCW surjectivity (E12.2) — ABSENT, the hard theorem.**
   0→μ_{p−1}→𝒲 →[Δ] ℤ_p⟦T⟧^{ψ=id}→0 with 𝒲 = (ℤ_p⟦T⟧^×)^{𝒩=id}. The
   authors call lem:B mod p 2 "the most delicate and technical part". Sub-leaves
   (source 3292–3379): lem:log der 1 (Δ𝒲 ⊆ ℤ_p⟦T⟧^{ψ=id}, via Δ∘φ = p·φ∘Δ
   — a NEW power-series identity — + φ∘𝒩 = ∏_{η∈μ_p} f((1+T)η−1) which is the
   §10 deferred Eqphipsi at the SERIES level, μ_p ⊂ ℂ_p); lem:log der red mod p
   (A=B ⟹ surjective, p-adic successive approximation + ℤ_p⟦T⟧^× compactness —
   the §10 compactness pays again); lem:A mod p (𝒲 mod p = 𝔽_p⟦T⟧^×, via
   `normOp` mod-p^k continuity (ii)(iv)); lem:B mod p + lem:B mod p 2 (the
   explicit 𝔽_p⟦T⟧ construction: induction building α_i ∈ 𝔽_p with
   h_m = (T+1)/T·h − Σ Δ(1−α_iT^i) ∈ T^{m−1}𝔽_p⟦T⟧, using d_n = d_{np} and
   ψ-fixing of (T+1)/T). SIZING: ~7–10 leaves, several hundred LOC, the
   hardest mathematics in Part II. The ψ=id/ψ=0 SERIES subspaces (only measure-
   level so far) must be introduced; the §10 deferred series-φ∘ψ / Eqphipsi
   comes fully due here.

## Other new pieces (medium/small)
- ℤ_p(1) = projlim μ_{p^n} (def:Zp(1)): ABSENT in mathlib — construct as a
  ℤ_p-module with 𝒢-action via χ. In our model it is `{(ξ_n^a)_n : a ∈ ℤ_p}`
  ⊂ 𝒰_∞ (the image identified in thm:fund exact seq's kernel computation).
- 𝒰_∞ = μ_{p−1} × 𝒰_{∞,1} (Teichmüller split): ABSENT in mathlib; the
  reduction-mod-𝔭_n SES `1→𝒰_{n,1}→𝒰_n→μ_{p−1}→1` splits (Teichmüller).
  We have `localUnitsOne` and the residue machinery; the split is new.
- lem:rest zp*: 0→ℤ_p→ℤ_p⟦T⟧^{ψ=id}→[1−φ] ℤ_p⟦T⟧^{ψ=0}→ℤ_p→0 — a series-level
  exactness (Σφ^n convergence + ker(1−φ) = constants), small once the series
  ψ-subspaces exist.
- Global generators (12.3): γ_{n,a}, half-power ξ^{(1−a)/2} via (2:ZMod p^n)⁻¹
  (p odd); cyclicity over ℤ[𝒢_n^+] needs the 𝒢_n^+-action (E12.1's finite
  level). lem:closure (12.4): p-adic closure = ℤ_p-span (compactness of ℤ_p^r +
  the zpPow binomial convergence — `zpPow` reused). LemmaGeneratorCinfty1.

## Scope decision (per-section discipline + honesty)
§12 is the LARGEST and DEEPEST section. The board is STAGED into clusters with
the two critical-path sub-developments (E12.1 Galois action, E12.2 thm:log der)
first, since everything downstream needs them. The final assembly (thm:iwasawa 2)
is the milestone. Two honest risk flags carried into the board:
- E12.1 requires realising mathlib's abstract `autEquivPow` on our concrete
  fixed-ξ ℂ_p-tower with tower-compatibility + levelNorm-commutation. If the
  compatibility proves to need the global number-field reduction (survey
  caveat), that becomes a sub-cluster — the board notes it.
- E12.2's lem:B mod p 2 is research-grade; it gets its own sub-leaves and is the
  expected Tier-A spawn point during execution.
The §11 statement-fix (a ≡ 1 mod p for principal-unit membership; b2-logged at
T1113) comes due here: thm:iwasawa 2's image computation uses
`coleman_to_kl` at the generator a, and the wγ_{n,a} correction (LemmaGenerator-
Cinfty1, the Teichmüller twist w making wγ_{n,a} ≡ 1 mod 𝔭_n) is EXACTLY the
principal-unit normalisation the §11 note flagged — §12.4 resolves it natively.

## Files (new directory PadicLFunctions/IwasawaProof/)
- `IwasawaProof/GaloisAction.lean` — E12.1: τ_{a,n} on K_n, tower-compat,
  levelNorm-commutation, the 𝒢-action on NormCompatUnits, σ_a on power series,
  f_{σ_a u} = σ_a f_u, Col 𝒢-equivariance.
- `IwasawaProof/Equivariance.lean` — 12.1: ℤ_p-equivariance of Col on 𝒰_{∞,1},
  μ_{p−1} × 𝒰_{∞,1} split, μ_{p−1} killed, the Λ(𝒢)-module structure + cor:G-eq.
- `IwasawaProof/LogDerivative.lean` — E12.2: thm:log der + all its lemmas; the
  series ψ=id/ψ=0 subspaces; Δ∘φ = p φ∘Δ; the 𝔽_p⟦T⟧ construction.
- `IwasawaProof/FundamentalSequence.lean` — 12.2 tail: lem:rest zp*, ℤ_p(1),
  thm:fund exact seq.
- `IwasawaProof/Generators.lean` — 12.3 + 12.4: γ_{n,a}, the generator lemmas,
  lem:closure, LemmaGeneratorCinfty1.
- `IwasawaProof/Main.lean` — 12.5: thm:iwasawa 2 (the MILESTONE), and wiring
  thm:iwasawa (§11's unwired node) to it.

## Deferred (§12 update)
- Full Λ(ℤ_p⟦T⟧)-module structure theorem (pseudo-isomorphism, characteristic
  ideals): mathlib has Weierstrass preparation only — NOT needed for thm:iwasawa
  2 (an isomorphism statement, not a structure-theorem application); it is §13
  (IMC) material. Stays deferred.
- The global Krull 𝒢 = Gal(F_∞/ℚ) ≅ ℤ_p^×: still the identified side
  (replan R11.1 continues); §12's "𝒢" is ℤ_[p]ˣ with c = −1, and the LOCAL
  finite Gal(K_n/ℚ_p) ≅ (ℤ/p^n)^× is realised concretely (E12.1) only as far
  as the action on the tower needs — no abstract global Galois group is built.
