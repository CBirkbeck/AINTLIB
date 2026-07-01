# Decomposition — DedekindResidue (Theorem 1 spine)

Source: Belabas–Friedman, *Computing the residue of the Dedekind zeta function*
(arXiv:1305.0035), `refs/ANCF/1305.0035.pdf`. This first pass captures the **paper's own
proof structure** for Theorem 1 and flags the three results the paper *cites without
proof* as deep sub-projects (SP1/SP2/SP3), each to be decomposed from its own reference
in a focused `/develop --decompose` pass.

## Skeleton location (builds clean; `lake build DedekindResidue.MainTheorem` ✓, 4 sorries)

- `DedekindResidue/AuxiliaryFunction.lean` — `gAux` (eq 6), `auxF` (eqs 11–12) — **sorry-free**
- `DedekindResidue/CompletedZeta/FunctionalEquation.lean` — `completedDedekindZeta`,
  `completedDedekindZeta_one_sub` — **stubs (SP1)**
- `DedekindResidue/CompletedZeta/GRH.lean` — `GeneralizedRiemannHypothesis` — **sorry-free**
- `DedekindResidue/MainTheorem.lean` — `bSum` (stub), `fK` (sorry-free modulo `bSum`),
  `belabas_friedman_thm1` (stub statement)

## Result R: `belabas_friedman_thm1` (Theorem 1)

### Source statement (verbatim, p. 2)
> "Let K be a number field of degree n > 1, let κ_K be the residue of the Dedekind zeta
> ζ_K(s) at s = 1, and let Δ_K be the absolute value of the discriminant of K. Assume GRH,
> i.e. that ζ_K(s) ≠ 0 and ζ_ℚ(s) ≠ 0 whenever Re(s) > 1/2. Then, for any real X ≥ 69, the
> difference |log κ_K − f_K(X)| is bounded above by
> (2.324 log Δ_K)/(√X log(3X)) · ((1 + 3.88/log(X/9))(1 + 2/√(log Δ_K))² + 4.26(n−1)/(√X log Δ_K))."

Lean ↔ source: `belabas_friedman_thm1` asserts exactly this, with `κ_K =
NumberField.dedekindZeta_residue K`, `Δ_K = |NumberField.discr K|`, `n = Module.finrank ℚ K`,
`GRH` = `GeneralizedRiemannHypothesis K` (the `ζ_K` side) `+ RiemannHypothesis` (the `ζ_ℚ`
side). Both are hypotheses, not axioms.

### Plain-English proof (paper, "Proof of Theorem 1", pp. 10–12)
Apply **Lemma 4** with `k = ℚ`, `a := log 9`, `T := log X` (the hypothesis `0 < a < T`
holds as `X > 9`). A short calculation gives `1/g(T) − 1/g(T−a) = 2√X log(3X)/3` (eq 20)
and `A(T) − A(T−a) = B_K(X) − B_K(X/9)`, so `f_K(X)` appears. Lemma 4 then bounds
`(2√X log(3X)/3)|log κ_K − f_K(X)|` by `c_{a,T} ∑_ρ^{K+ℚ} 1/(¼+γ_ρ²) + (n_K−n_ℚ)a
e^{−(T−a)/2} β(T−a)` (eq 21). The zero-sum over `ζ_ℚ` is classical (`= 0.023095…`); the
zero-sum over `ζ_K` is bounded by **Lemma 5** (Landau–Stark) using `σ = 1 + (log Δ_K)^{−1/2}`,
giving `(√(log Δ_K) + 2)²`. Collecting constants (`X ≥ 68.1`, `β(log(X/9)) < 1`) yields the
three numerical constants `3/2(1+log9/4) < 2.324`, `6/(1+log9/4) < 3.88`,
`3log9/(1+log9/4) < 4.26`.

### Dependency tree (mirrors the paper)

- **R** `belabas_friedman_thm1` (Thm 1, pp. 10–12)
  - **L4** `lemma4` — the "`T` and `T−a`" trick (Lemma 4, eqs 14–17, pp. 7–9). *Internal.*
    Source proof uses the mean value theorem on `sin(γT)`, the decreasing integrals
    `q(T)`, `q̃(T)` (eq 17), and the decreasing `β(U)`. Uses GRH (`γ_ρ ∈ ℝ`).
    - **L3** `lemma3` — explicit formula applied to `F_{s,X}` (Lemma 3, eq 13, pp. 5–7).
      *Internal.* Valid for `Re s > 1` by the explicit formula; continued to `Re s > ½`
      by analytic continuation (GRH gives `γ² + h² ≠ 0`).
      - **L2** `fourier_auxF` — Fourier transform `F̂_{s,X}` (Lemma 2, eq 8, pp. 5–6).
        Leaf-ish: elementary calculus (two integrations by parts, eq 7) once `auxF` and
        the Fourier integral are in place. → depends on `auxF` (done) + mathlib Fourier.
      - **AG-SP2** the Weil–Poitou **explicit formula** (eqs 1, 3, p. 3). **API GAP.**
      - **[Euler product]** `−ζ'_K/ζ_K = Σ Λ_K` for `Re s > 1` → **Chebotarev**
        `NumberFieldEulerProduct` (leaf, project).
    - **AG-SP3** **Stark's formula** (Lemma 5, eq 19, pp. 8–11): `Σ_ρ 1/(σ−ρ) =
      ½log Δ_K + 1/(σ−1) + 1/σ − ½ d_{K,σ}`, and `Σ_ρ (¼+γ_ρ²)^{−1} = O(log Δ_K)`.
      **API GAP.**
  - **[classical ζ_ℚ zero sum]** `Σ_ρ (¼+γ_ρ²)^{−1} = C/2 + 1 − log(4π)/2 = .023095…`
    (p. 11, Davenport §12) → mathlib `RiemannHypothesis` + Riemann-ζ zeros (leaf).
  - **[bridge]** `fK`, `bSum` (`f_K`, `B_K`, p. 2) — project defs; `Residue.lean` ties the
    bound to `log(h_K R_K)` via `dedekindZeta_residue`.

### API gaps — each needs its own reference-driven sub-decomposition

- **SP1** (foundation, under L3/L4/SP2/SP3): general-`K` completed `ζ_K`, meromorphic
  continuation, functional equation `Λ_K(s)=Λ_K(1−s)`, Hadamard product / zero set.
  Not in mathlib (only ℚ, Dirichlet-L; cyclotomic in FltRegularBernoulli). **Route
  (chosen):** mirror mathlib `AbstractFuncEq`/`RiemannZeta` + FltRegularBernoulli
  cyclotomic, via the theta function over the Minkowski ideal lattice + Poisson
  summation. Skeleton stubs: `completedDedekindZeta`, `completedDedekindZeta_one_sub`.
- **SP2** the Weil–Poitou explicit formula (AG-SP2). Depends on SP1. **Route:**
  Poitou (Numdam) / Lang *ANT* Ch. XVII / Iwaniec–Kowalski §5 — contour integral of
  `−Λ'_K/Λ_K` against a test function.
- **SP3** Stark's formula (19) + Landau–Stark bound (AG-SP3). Depends on SP1 (log-derivative
  of the FE + Hadamard product). **Route:** Stark 1974 eq (9); Landau §180.

### Notes on faithfulness
- The paper's proof of Theorem 1 is self-contained **given** the explicit formula (SP2),
  Stark's formula (SP3) and the analytic substrate (SP1); it does not prove those. Per the
  source-faithfulness rule, SP1/SP2/SP3 are decomposed from *their own* references, not
  invented from this paper. Their per-leaf trees (with verbatim quotes + adversarial passes)
  are authored in their focused passes.
- L2 (`fourier_auxF`) is the one spine leaf dischargeable now from mathlib (Fourier +
  `auxF`); it is the natural first Tier-3 target once SP-independent.
