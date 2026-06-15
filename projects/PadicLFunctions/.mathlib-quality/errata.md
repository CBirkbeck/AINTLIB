# Errata and formalisation notes for RJW (arXiv:2309.15692)

Mistakes, typos, and glossed gaps in Rodrigues Jacinto–Williams, *An
introduction to p-adic L-functions*, found while formalising. Line numbers
refer to `.mathlib-quality/references/2309.15692-padic-L-functions.tex`.
Maintained as found (standing rule, CLAUDE.md). Three severity classes:
**typo** (wrong as printed, fix obvious), **gap** (statement or proof needs
an argument/hypothesis the notes don't supply), **subtlety** (correct as
mathematics, but the implicit framework hides real content that
formalisation had to make explicit).

## Typos

1. **TeX 2009 (§6.1, proof of Thm 6.1(i))** — typo. The opening display
   reads `L(θ,s) = Σ_{a ∈ (ℤ/Nℤ)ˣ} θ(a) Σ_{n ≡ a mod D} n^{−s}`; the inner
   congruence should be **mod N**, not mod D (D is the tame conductor of
   §6.2; the indicator computed two lines later is correctly mod N).

2. **TeX 2122 (§6.2, proof of Thm 6.1(ii), case split)** — off-by-one. The
   two cases are stated as "First assume that **n > 1**, so that χ ≠ 1" and
   "Now assume n = 0"; the case n = 1 is skipped as printed. The first case
   should read **n ≥ 1** (the argument is verbatim the same).

3. **TeX 1952 (§5.3, proof of Thm 5.19)** — dropped ω⁻¹. The first line of
   the aligned display reads `∫_{ℤ_p^×} χ(x)⟨x⟩^{k−1}·μ_η = ∫ χω^{−k}(x)
   x^{k−1}·μ_η`; by eq:alternative (TeX 1987) the left-hand side should be
   `∫ χω^{−1}(x)⟨x⟩^{k−1}·μ_η` — exactly the quantity the preceding
   sentence computes.

4. **TeX 1934 (§5.3, remark after Def 5.18)** — LaTeX glitch: `\begin{remark}
   \item An equivalent definition is …` has an `\item` with no enclosing
   list environment.

5. **TeX 2146 (§6.2, case n = 0)** — wording: "the assignment c ↦ c' = pc
   defines an automorphism of (ℤ/Nℤ)ˣ". Multiplication by p is a bijection
   of the unit set (and an automorphism of the additive group), but not a
   group automorphism of (ℤ/Nℤ)ˣ. Only bijectivity is used.

12. **TeX 2839 (§10.3, Thm coleman to kl) vs TeX 2614 (Lem relate cyclo to
    mua) + TeX 1568 (Def DefZetap)** — dropped sign. Thm coleman to kl is
    stated `ζ_p = Col(c(a))/θ_a` (no sign). But the construction gives the
    opposite sign: by Def coleman map (TeX 2829) `Col(c(a)) = x⁻¹·Res_{ℤ_p^×}
    (𝒜⁻¹(∂log f_{c(a)}))`, and `∂log f_{c(a)} = (a−1) − F_a` (prop:coleman
    zetap, TeX 2595–2608) so by the notes' *own* Lem relate cyclo to mua (TeX
    2611–2624) `Res_{ℤ_p^×}(μ_{∂log f_{c(a)}}) = −Res_{ℤ_p^×}(μ_a)`, whence
    `Col(c(a)) = −x⁻¹Res(μ_a)`. Def DefZetap (TeX 1565–1568) sets `ζ_p =
    (x⁻¹Res μ_a)/θ_a` with `θ_a = [a]−[1]` (TeX 1551). Composing: the display
    at TeX 2839 would give `ζ_p = −(x⁻¹Res μ_a)/θ_a`, contradicting DefZetap.
    The correct identity carries a minus: **`ζ_p = −Col(c(a))/θ_a`**,
    equivalently `([a]−[1])·ζ_p = −Col(c(a))`. (The minus is exactly the
    minus the notes already record in Lem relate cyclo to mua; it is simply
    not carried into the Thm coleman to kl display. `θ_a` is *not*
    sign-flipped — TeX 1551 fixes it as `[a]−[1]`, matching our denominator.)
    Formalised in the honest-sign form (`coleman_to_kl`, Coleman/Map.lean;
    the core `Col(c(a)) = −zetaNum a` is `Col_cyclo`).

13. **TeX 3038 (§11.1, proof of the corollary "ζ_p is a pseudo-measure on
    𝒢⁺")** — wrong at k = 1. The proof reads "This follows from the
    interpolation property, as ζ(1−k) = 0 for odd k ≥ 1"; but
    ζ(1−1) = ζ(0) = −1/2 ≠ 0. What vanishes for *all* odd k ≥ 1 is the
    *interpolated moment* (1−p^{k−1})·ζ(1−k): at k = 1 via the Euler factor
    1−p⁰ = 0, at odd k ≥ 3 via ζ(1−k) = −B_k/k = 0. (The preceding text at
    TeX 2992 hedges with "vanishes at the characters χ^k, for any odd
    integer k > 1" — but the membership criterion the corollary leans on
    (TeX 3019–3022) needs all odd k ≥ 1, so the k = 1 case cannot be
    skipped.) Formalised with the Euler-factor case split
    (`padicZeta_odd_moment_eq_zero`, Iwasawa/ZetaGalois.lean).

## Gaps

6. **Thm 6.1(ii) at tame conductor D = 1 (TeX 1987–1995 vs §5.2 standing
   hypotheses)** — scope gap. The theorem is stated for every non-trivial
   θ = χη, but the proof routes through μ_η/F_η, whose construction
   (TeX 1793–1798) carries §5.2's standing assumption **D > 1** ("η has
   conductor D, where D > 1"): at D = 1 the defining series has denominators
   `(1+T)ε_D^c − 1` with ε_D = 1, i.e. `T`, which is not invertible, and the
   correct object is the χ-twist of the *pseudo-measure* ζ_p. The pure
   p-power-conductor case needs its own (short) argument the notes don't
   give. Formalisation: `LpFunction_one` is stated for D > 1 (replan R6.4);
   D = 1 deferred.

7. **TeX 2040–2044 (§6.1, evaluation at s = 1)** — convergence gloss. "we
   may consider the Taylor series expansion −log(1−ε^c) = Σ ε^{nc}/n.
   Substituting this into (eq. 6.1), we see the series converges at s = 1
   to the required result." The series is only **conditionally** convergent
   on the unit circle, the substitution is at the boundary of the halfplane
   of convergence, and identifying `lim_{s→1⁺} Σ ε^{nc} n^{−s}` with
   `Σ ε^{nc}/n` requires an Abel-type limit theorem for Dirichlet series
   (which mathlib lacked; formalised as `tendsto_LSeries_pow_boundary`).
   Standard, but a genuine analytic step, not a substitution.

14. **TeX 2581–2585 / 3407–3418 (§9 norm collapse, §12.2.2 ℤ_p(1)) — the
    `pow`-norm and the ℤ_p(1) Tate-twist tower require `p` odd.** The §9
    minimal-polynomial computation gives `N_{n+1,n}(ξ_{p^{n+1}}^k) =
    (−1)^{[K_{n+1}:K_n]}·(−ξ_{p^n}^k) = (−1)^{p+1}·ξ_{p^n}^k`, which is
    `ξ_{p^n}^k` only for **p odd** (p+1 even); for `p = 2` and `k` odd it is
    `−ξ_{p^n}^k` (concretely `N_{ℚ₂(i)/ℚ₂}(i) = i·(−i) = 1 ≠ −1 = ξ_1`). Hence
    the norm-compatibility of the integral Tate twist `ℤ_p(1) = {(ξ_n^a)_n}`
    (RJW def:Zp(1), the claim `N_{n+1,n}(ξ_{n+1}^a) = ξ_n^a`) is **false at
    p = 2**, matching §9/§12's standing "p odd" (TeX 2470). The notes never
    flag this hypothesis on the twist tower itself. Formalisation: the project
    threads `hp2 : p ≠ 2` as an explicit hypothesis everywhere in §9/§12 (e.g.
    `levelNorm_zetaSys_pow_sub_one`); the substrate
    `levelNorm_zpPow_zetaSys` in `IwasawaProof/FundamentalSequence.lean` is
    *missing* this `hp2` and is therefore unprovable as currently stated (its
    forward consumers `normOp_binomialSeries` / `mem_ker_Col_iff_mem_ZpOne` are
    correspondingly false at p = 2). Redraft note: `levelNorm_zpPow_zetaSys`,
    `normOp_binomialSeries`, `colemanSeries_eq_binomialSeries_of_mem_ZpOne`'s
    consumer `mem_ker_Col_iff_mem_ZpOne` should all carry `hp2 : p ≠ 2`.

## Subtleties surfaced by formalisation

8. **Eqphipsi on unbounded series (used at TeX 2128–2134)** — the formula
   `(φ∘ψ)F = p⁻¹ Σ_{ξ∈μ_p} F((1+T)ξ−1)` is applied to F̃_θ ∈ ℛ⁺. As a
   *formal* power-series identity the right side is ill-formed (the
   substitution T ↦ (1+T)ξ−1 has non-nilpotent constant term ξ−1 for
   ξ ≠ 1); it is an identity of rigid-analytic functions on the open disc.
   Formalisation realises it as a convergent-evaluation statement
   (`sum_seriesEval_mahlerK`, decomposition replan R6.6).

9. **The ψ/digit decomposition is integral (relevant to §3.5.5 and the §6
   use of ψ on F̃_θ)** — the unique decomposition `F = Σ_{i<p} (1+T)^i·
   φ(F_i)` underlying ψ holds over ℤ_p-type (p-adically complete integral)
   coefficient rings but is **false** over a field containing 1/p: there
   `(1+T)^p − 1` has unit linear coefficient, φ is bijective, and digits
   are wildly non-unique (counterexample over ℚ, p = 2, recorded in
   b2_log.jsonl T605). The notes never need the field-coefficient version,
   but any reading of ψ as "defined on all of K⟦T⟧" is wrong; the §6
   computation must (and, reorganised, does) run through integral or
   evaluated forms only.

10. **RJW Thm 5.17's "in particular" (TeX 1927, remark after the theorem)**
    — "ζ_{p,i} is identically zero whenever i is odd" follows from the
    interpolation formula *plus* density of the interpolation points *plus*
    continuity of ζ_{p,i} in s; the notes present it as immediate. (Prose
    remark only; recorded in the blueprint node note.)

11. **TeX 2403 (§8, Theorem, part (a))** — gap/imprecision. "(a) A₀ is a
    pseudo-measure" with A₀ = xζ_p/2 (TeX 2410). With the notes' own
    Definition 3.34 (λ ∈ Q(G) is a pseudo-measure iff ([g]−[1])·λ ∈ Λ(G)
    for **all** g), the twist x·ζ_p is *not* a pseudo-measure: the x-twist
    τ : [g] ↦ g[g] is a ring automorphism of Λ(ℤ_p^×), so
    ([g]−[1])·τ(ζ_p) = τ((g⁻¹[g]−[1])·ζ_p), and g⁻¹[g]−[1] =
    g⁻¹([g]−[1]) − (1−g⁻¹)[1] has augmentation g⁻¹−1 ≠ 0 — it does not lie
    in the augmentation ideal, so (g⁻¹[g]−[1])ζ_p = (∈ Λ) − (1−g⁻¹)·ζ_p ∉ Λ
    (a nonzero scalar multiple of ζ_p is never in Λ: the §7 pole is real).
    The pole of xζ_p sits at the character x⁻¹, not at the trivial
    character. Correct statement: **(g·[g]−[1])·A₀ ∈ Λ(ℤ_p^×) for all g**
    (the x-twisted augmentation ideal kills A₀); equivalently A₀ ∈ τ(image
    of the pseudo-measures). Formalised in that corrected form
    (`twistedZetaHalf_isTwistedPseudoMeasure`, EisensteinFamily.lean).

---
*Add new entries as found; cite TeX line numbers and, where applicable, the
b2_log.jsonl entry and the Lean declaration that resolves the issue.*
