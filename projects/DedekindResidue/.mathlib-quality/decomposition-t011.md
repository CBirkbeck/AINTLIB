# Decomposition — T011 (Lemma 4) + L5 (Landau–Stark) + T012 (Theorem 1)

**Source**: `refs/DedekindResidue/bf-src/paper.tex` (B–F 1305.0035 TeX source, fetched
2026-07-03; line numbers below refer to it). Strategy fixed against the paper verbatim.

## The route (paper §3, lines 323–643)

Our `lemma3_display` (Lemma3.lean) is the per-field, real-σ>1, ×2-scaled form of the
paper's eq (13) `\label{eq:Explicit1}` (lines 330–346): B–F (13) = (display_K −
display_k)/2 with the plateau sum NOT divided by g. B–F prove (13) for Re s > 1 first
(our regime), then analytically continue to Re s > 1/2 (lines 377–388). **WE AVOID THE
CONTINUATION**: Lemma 4 only consumes (13) at s = 1, and its LHS is the limit
κ_{K/k} = lim_{s→1} log(ζ_K/ζ_k)(s) — so we prove the σ-version of every Lemma-4
estimate at real σ ∈ (1, 2] with h = σ−1/2 tracked, and take σ → 1⁺ in the final
INEQUALITY (limits of both sides), never continuing the identity itself.

### Lemma 4 = `Mostways` (lines 409–519, verbatim statement)
For K/k with RH for ζ_K, ζ_k, 0 < a < T:
|((1/g(T)) − 1/g(T−a))·log κ_{K/k} − A(T) + A(T−a)|
  ≤ (n_K−n_k)·a·e^{−(T−a)/2}·β(T−a) + c_{a,T}·Σ_ρ^{K+k} 1/(¼+γ_ρ²)
with g(t) = e^{−t/2}/t, A(t) = Σ_{N𝔭^m<e^t}^{K−k} (log N𝔭/N𝔭^{m/2})(g(m log N𝔭)/g(t) − 1),
c_{a,T} = 1 + a/4 + 6/(T−a), β(t) = ½(½+1/t)e^t log((e^t+1)/(e^t−1)).

Proof estimates (all at s=1 in the paper; we do them at real σ with h-tracking):
1. **sin-diff (lines 446–456)**: MVT |sin(γT)−sin(γ(T−a))| ≤ |γ|a ⟹
   h²·Σ|sin-diff|/((h²+γ²)|γ|) ≤ a·Σh²/(h²+γ²); at h=½: (a/4)·Σ1/(¼+γ²).
   σ-version: Σh²/(h²+γ²) ≤ (9/4)Σ1/(¼+γ²) domination for h ∈ [½,3/2] and →(a/4)Σ
   as σ→1 (dominated convergence).
2. **cos terms (lines 457–459)**: trivial bound |cos| ≤ 1 per T and T−a:
   (h+1/T) + (h+1/(T−a)) ≤ 1 + 2/(T−a) at h=½.
3. **int terms (lines 460–467)**: |2∫_T^∞ ((t/2+1)/t²)cos(γt)f_{1,X}| ≤ 2/T via the
   exact antiderivative from eq:diffeq (g_s' = −(h+1/t)g_s): ∫(½+1/t)(Te^{T/2}/(te^{t/2}))
   = T e^{T/2}·[−e^{−t/2}/t]_T^∞ = 1. Sum of both cutoffs ≤ 2/(T−a)+2/T ≤ 4/(T−a);
   TOTAL of 2+3: 1 + 2/(T−a) + 4/(T−a) = 1 + 6/(T−a) — wait, paper: c_{a,T} = 1 + a/4
   + 6/(T−a) aggregates 1(from cos) + a/4(sin) + [2/(T−a) from cos-1/T-parts +
   4/(T−a) from int] = 6/(T−a) ✓ (their line 459: ½+1/T+½+1/(T−a) < 1+2/(T−a); their
   int: 2/T + 2/(T−a) < 4/(T−a)).
4. **q/q̃ archimedean (lines 476–518)**: q(T) := ∫_T^∞(1−f_{1,X})/2sinh(t/2), q̃ cosh;
   −q'(T) = ∫_T^∞ (1+T/2)e^{T/2}/(t(e^t−1)) ≤ (½+1/T)e^{T/2}·(−log(1−e^{−T}))
   (eq:deriv); |q̃'| ≤ (½+1/T)e^{T/2}log(1+e^{−T}); q,q̃ decreasing; MVT on [T−a,T]:
   |((n_K−n_k)/2)(q(T)−q(T−a)) + ((r_K−r_k)/2)(q̃-diff)| ≤ (n_K−n_k)a e^{−U/2}β(U)
   ≤ (n_K−n_k)a e^{−(T−a)/2}β(T−a) (β decreasing; |r_K−r_k| ≤ n_K−n_k via n_K ≥ 2n_k,
   lines 497–501). ½L_{K/k} cancels in the difference (line 475).
5. **LHS limit σ→1⁺ (our addition)**: log(ζ_K/ζ_ℚ)(σ) = log((σ−1)ζ_K(σ)) −
   log((σ−1)ζ_ℚ(σ)) → log κ_K − log κ_ℚ = log κ_K via mathlib
   `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT` + `dedekindZeta_residue ℚ = 1`
   + our real-ray positivity (`dedekindZeta_ofReal_re_pos`). Plateau sums: finite,
   each term continuous in σ at 1 (exp/rpow continuity) → A(T) etc.
   Zero sums: dominated convergence over ZetaZeros with majorant (9/4)m_ρ/(¼+γ²)
   (b4 at h=½).

### Lemma 5 = `Estimate` (lines 523–562, verbatim)
σ>1, RH(ζ_K): Σ_ρ 1/(¼+γ_ρ²) ≤ (2σ−1)(log Δ_K + 2/(σ−1) − d_{K,σ}),
d_{K,σ} := −2ζ'_K/ζ_K(σ) + n_K(log 2π − Ψ(σ)) + r_K(Ψ((σ+1)/2)−Ψ(σ/2))/2 − 2/σ.
Proof: 1/(¼+γ²) < 4h²/(h²+γ²) (h>½); h·Σ1/(h²+γ²)... reduces to **eq:Stark
(lines 554–557)**: Σ_ρ 1/(σ−ρ) = ½log Δ_K + 1/(σ−1) + 1/σ − ½d_{K,σ}.
**Footnote (lines 549–553): eq:Stark is provable with the explicit formula at
F(x) := exp(−(σ−½)|x|)** — OUR ROUTE (we have no Weierstrass/Hadamard theory; we have
the full weil machinery + the digamma integral bridges). Φ_F(z) = 2h/(h²−(z−½)²);
zero side Σ m_ρ·2h/(h²+γ²); prime side H(0) relates to −ζ'/ζ(σ) (kernel collapse:
log N·N^{−m/2}e^{−h·m log N} = log N·N^{−mσ}); Γ-side sinh/cosh integrals evaluate to
the Ψ-differences via `digamma_sub_digamma_eq_integral` (GammaSide, PROVEN); the
weil hypotheses at F need a NEW discharge suite (BV/decay/band bounds — all easier
than auxF: no kink except at 0, pure exponential).

### Theorem 1 endgame (lines 564–631, verbatim)
k=ℚ, a=log 9, T=log X, X>9: 1/g(T)−1/g(T−a) = (2/3)√X log(3X) (eq:Diff, elementary:
e^{T/2}T − e^{(T−a)/2}(T−a) = √X logX − (√X/3)(logX−log9) = (√X/3)(3logX−logX+log9)
= (√X/3)·log(X²·9) = (2√X/3)log(3X) ✓). A(T)−A(T−a) = B_K(X)−B_K(X/9);
κ_{K/ℚ} = κ_K. eq:Step1: (2√Xlog3X/3)|logκ_K − f_K(X)| ≤ c_{a,T}Σ^{K+ℚ}1/(¼+γ²) +
(n−1)·a·e^{−(T−a)/2}β(T−a), noting (n−1)·log9·e^{−(T−a)/2} = 3(n−1)log9/√X.
ζ_ℚ-zero sum: paper uses the classical value 0.023095; WE ONLY NEED
ζℚsum − (2σ−1)d_{K,σ} < 0, via d_{K,σ} > 2log(2π) − 2Ψ(4) = 1.163 (lines 603–612;
uses ζ'_K/ζ_K(σ)<0, n_K≥2, Ψ increasing, Ψ(4) = 11/6 − γ_E) and a NUMERIC bound
ζℚsum ≤ 1.163 (derivable from OUR Lemma 5 at K=ℚ, σ=2: (2σ−1)(2/(σ−1)−d_{ℚ,2}) =
3(2−d_{ℚ,2}) ≈ 0.41 — needs certified numerics for ζ'/ζ(2), Ψ(1),Ψ(3/2),Ψ(2),
γ_E bounds).
σ := 1 + 1/√(logΔ_K) (needs Δ_K ≥ 3, i.e. K ≠ ℚ from n>1 — mathlib: Hermite/Minkowski
`discr` bound? |Δ| ≥ 3 for n ≥ 2: mathlib has `NumberField.abs_discr_gt_two` (n≥2 ⟹
|Δ|>2? check name) ⟹ (2σ−1)(logΔ+2/(σ−1)) = (√logΔ+2)². β(log(X/9)) < 1 for
X ≥ 68.1 (numeric monotonicity of β). Final: pull out (1+log9/4)logΔ, constants
3/2(1+log9/4) < 2.324, 6/(1+log9/4) < 3.88, 3log9/(1+log9/4) < 4.26.

## Leaf order
- **L4-a**: relative σ-display for K/ℚ (lemma3_display K − lemma3_display ℚ; needs
  the ℚ-instance facts: Δ_ℚ = 1 (log = 0), n_ℚ = r₁(ℚ) = 1, r₂(ℚ) = 0).
- **L4-b**: T vs T−a difference of L4-a at fixed σ (pure algebra).
- **L4-c1..c4**: the four σ-tracked estimates (sin/cos/int/arch).
- **L4-d**: σ→1⁺ limits (LHS via residues; zero sums dominated; assemble Explicit2
  with k=ℚ).
- **L5-a**: the discharge suite at F_h(x) = e^{−h|x|} (weil hypotheses).
- **L5-b**: Φ_{F_h} closed form + the three sides' evaluation → eq:Stark(σ).
- **L5-c**: Estimate from eq:Stark (elementary, lines 537–547 conjugate-pair trick:
  under GRH Σh/(h²+γ²) = ΣRe(1/(σ−ρ)); note OUR zero index is the divisor of the
  ENTIRE completion H = s(s−1)Λ — H has NO zeros at 0,1 beyond ζ's; ζ_K's nontrivial
  zeros = zeros of H ✓ already our convention).
- **T12-a**: eq:Diff + A↔B_K bridge + Step1.
- **T12-b**: numeric layer (β mono + < 1 at 69; d_{K,σ} > 1.163; ζℚsum ≤ 1.163;
  γ_E/Ψ/ζ'(2) certified bounds).
- **T12-c**: final assembly `belabas_friedman_thm1`.
