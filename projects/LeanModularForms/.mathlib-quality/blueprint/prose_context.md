# Prose Context for Blueprint Authoring — Hecke Rings & Strong Multiplicity One

This is the **single source of truth** for every per-chapter blueprint worker. Read it in
full. Do **not** re-read the source papers individually.

## Project narrative

The project builds the abstract Hecke ring of a *Hecke pair* `(G, H, Δ)` as the free
ℤ-module on the double cosets `H\Δ/H`, with a convolution product whose structure
constants count coset overlaps (Shimura's Proposition 3.2). It proves this is an
associative unital ring, equips it with a degree ring-homomorphism, and gives a clean
criterion for commutativity: an *anti-involution* of the Hecke pair that fixes every
double coset makes the ring commutative. Specialising `(G,H,Δ) = (GL₂(ℚ), SL₂(ℤ),
Δ⁺∩M₂(ℤ))` and taking the **transpose** `g ↦ ᵗg` as the anti-involution proves the GL₂
Hecke algebra is commutative. The generators `T(a,d)` and `T(m) = Σ_{a|m} T(a, m/a)`
then satisfy **Shimura's multiplication table (Theorem 3.24)**: `T(1)=1`, the prime-power
recursion `T(1,pᵏ) = T(pᵏ) − T(p,p)·T(p^{k-2})`, the prime-power product
`T(pʳ)T(pˢ) = Σ pⁱ T(pⁱ,pⁱ) T(p^{r+s-2i})`, full multiplicativity
`T(m)T(n) = Σ_{d | (m,n)} d·T(d,d)·T(mn/d²)`, and the degree formulas. Because the Hecke
algebra is commutative, modular forms can be simultaneously diagonalised; the eigenvalue
systems are rigid enough to prove **Strong Multiplicity One (Miyake Theorem 4.6.12)**: a
normalised newform `f` and any cusp-form Hecke eigenfunction `g` sharing `f`'s eigenvalues
for almost all `n` must satisfy `g = c·f`.

## Notational conventions (use these in the LaTeX, NOT the Lean identifiers)

- `(G, H, \Delta)` — a **Hecke pair**: a group `G`, a subgroup `H`, and a submonoid `\Delta`
  with `H \le \Delta \le \operatorname{Comm}(H)` (the commensurator). Lean: `HeckePair`,
  fields `H`, `Δ`.
- `H \backslash \Delta / H` — the set of **double cosets** `HgH`. Lean: `HeckeCoset`.
- `Hg` (left cosets inside a double coset) — Lean: `HeckeLeftCoset`.
- `\mathcal{H}(G,H,\Delta)` or `\mathbb{T}` — the **Hecke ring**, the free ℤ-module on
  double cosets. Lean: `𝕋 P ℤ`. For GL_n write `\mathcal{H}_n`. Lean: `HeckeAlgebra n`.
- `T_g` or `[HgH]` — the **basis element** of `\mathbb{T}` attached to the double coset
  `HgH`. Lean: `T_single`.
- `\mu(g_1, g_2; d)` — the **structure constant** (Shimura's multiplicity): the number of
  pairs of left-coset reps whose product lies in the left coset of `d`. Lean:
  `heckeMultiplicity`.
- `\deg` — the **degree** homomorphism `\mathbb{T} \to \mathbb{Z}` sending `[HgH]` to the
  number of left cosets `Hg_i` it contains. Lean: `deg`, `HeckeCoset_deg`.
- `\bar{g}` — the image of `g` under an **anti-involution** `\iota`. Lean: `AntiInvolution.bar`.
- For GL₂: `T(a,d)` = double-coset basis element of `\mathrm{diag}(a,d)` with `a \mid d`
  (Lean `T_ad`); `T(m) = \sum_{a \mid m} T(a, m/a)` (Lean `T_sum`); `T(p,p)` the scalar
  class (Lean `T_pp`); `T(p) = T(1,p)`. Diagonal class `T_diag`, its basis element `T_elem`.
- `S_k(\Gamma_1(N))` — weight-`k` cusp forms; `S_k(N,\chi) = S_k(\Gamma_1(N),\chi)` the
  **Nebentypus `χ`-eigenspace** under the diamond operators `\langle d\rangle`
  (Lean `cuspFormCharSpace`; modular-form version `modFormCharSpace`).
- `S_k^{\flat}(N,\chi)` / `S_k^{\sharp}(N,\chi)` — the **old** / **new** subspaces
  (Lean `cuspFormsOld` / `cuspFormsNew`); projections `oldPart` / `newPart`.
- `a_n(f)` — the `n`-th Fourier coefficient (period-1 `q`-expansion); `a_1(f)` the leading
  one; `\lambda_n(f)` the classical Hecke eigenvalue. A **newform** is normalised: `a_1 = 1`.
- `T(n) f = \lambda_n f` — eigenform relation (Lean `Eigenform`, `heckeT_n_cusp`,
  `Eigenform.eigenvalue`). `\langle n\rangle` is the diamond operator; on `S_k(N,\chi)` it
  acts by `\chi(n)`, and `\lambda_n = \chi(n)\,\nu_n` relates the classical eigenvalue to
  the ring eigenvalue `\nu_n` (Lean `ringEigenvalue`).

## Notation rules for unformalisation

- DROP Lean plumbing: `[NeZero N]`, `{k : ℤ}`, `(mapGL ℝ)`, `.toModularForm'`,
  `.toCuspForm`, `ModularFormClass.qExpansion (1 : ℝ)`, `⟦·⟧` quotient brackets,
  `Submonoid`/`Subgroup` coercions, `Nat.card`, `Finsupp`. These are implementation, not
  mathematics.
- `ℕ+` is "a positive integer"; `Nat.Coprime n.val N` is "`(n,N)=1`".
- Write `\mid` for `∣`, `\to`/`\mapsto` for `→`/`↦`, `\sum` for `∑`, `\backslash` for the
  double-coset slash. Never put camelCase identifiers, `:=`, `→` (raw), or `[...]`
  typeclass brackets inside a `\begin{theorem}` body — that is forbidden unformalisation.

## GLOBAL LABEL MAP (authoritative — use EXACTLY these labels)

When you author a declaration, use the label in column 2. When your statement or proof
**depends on** another declaration, put its label in `\uses{}`. Cross-chapter references
are expected and resolve in the cross-link pass — always use the label spelled here.

The `\lean{}` name in column 3 is my best determination; **verify it** against the
`namespace`/`open` context at the top of the cited file before emitting (the worker has
the file). Use the fully-qualified name.

### Ch.1 `01_hecke_pairs.tex` — `AbstractHeckeRing/Basic.lean`
| Math object | label | `\lean{}` name | line |
|---|---|---|---|
| Hecke pair | `def:hecke-pair` | `HeckeRing.HeckePair` | 67 |
| double-coset set | `def:hecke-coset` | `HeckeRing.HeckeCoset` | 84 |
| left-coset set | `def:hecke-left-coset` | `HeckeRing.HeckeLeftCoset` | 98 |
| Hecke ring (underlying module) | `def:hecke-ring-carrier` | `HeckeRing.𝕋` | 364 |
| Hecke module | `def:hecke-module` | `HeckeRing.HeckeModule` | 372 |
| left-coset decomposition (Fintype) | `def:decomp-quot` | `HeckeRing.decompQuot` | 383 |
| `HgH = ⊔ Hgᵢ` | `lem:dc-eq-iUnion-lc` | `HeckeRing.DoubleCoset.doubleCoset_eq_iUnion_leftCosets` | 289 |

### Ch.2 `02_ring_structure.tex` — `Module/Multiplication/Ring/Associativity.lean`
| Math object | label | `\lean{}` name | line/file |
|---|---|---|---|
| product map on reps | `def:mulMap` | `HeckeRing.mulMap` | Multiplication 166 |
| structure constant `μ(g₁,g₂;d)` | `def:hecke-multiplicity` | `HeckeRing.heckeMultiplicity` | Multiplication 174 |
| structure-constant Finsupp `m` | `def:m-finsupp` | `HeckeRing.m` | Multiplication 589 |
| basis element `T_g` | `def:T-single` | `HeckeRing.T_single` | Multiplication 610 |
| product formula | `lem:mul-def` | `HeckeRing.mul_def` | Multiplication 605 |
| `T_{D₁}·T_{D₂}` expansion | `lem:T-single-mul` | `HeckeRing.T_single_mul_T_single` | Ring 112 |
| associativity | `lem:mul-assoc` | `HeckeRing.mul_assoc_𝕋` | Ring 28 |
| identity `T_{[H]}` | `lem:one-def` | `HeckeRing.one_def` | Ring 45 |
| ring instance | `thm:hecke-ring` | `HeckeRing.instRing` | Ring 80 |
| module action `T·m = Σ…` | `lem:smul-eq-sum` | `HeckeRing.smul_eq_sum` | Module 106 |

### Ch.3 `03_degree.tex` — `AbstractHeckeRing/Degree.lean`
| Math object | label | `\lean{}` name | line |
|---|---|---|---|
| degree of a double coset | `def:hecke-coset-deg` | `HeckeRing.HeckeCoset_deg` | 50 |
| `#` left cosets in `g·βH`-orbit | `lem:smulOrbit-card` | `HeckeRing.smulOrbit_card` | 94 |
| degree ring hom | `def:deg` | `HeckeRing.deg` | 197 |
| `deg(fg)=deg f·deg g` | `lem:deg-mul` | `HeckeRing.deg_mul` | 216 |

### Ch.4 `04_commutativity.tex` — `Commutativity.lean` + `GLn/TransposeAntiInvolution.lean`
| Math object | label | `\lean{}` name | line/file |
|---|---|---|---|
| anti-involution | `def:anti-involution` | `HeckeRing.AntiInvolution` | Comm 27 |
| induced map on double cosets | `def:onHeckeCoset` | `HeckeRing.AntiInvolution.onHeckeCoset` | Comm 85 |
| fixes ⇒ commutes | `thm:mul-comm-of-ai` | `HeckeRing.AntiInvolution.mul_comm_of_antiInvolution` | Comm 472 |
| CommRing from anti-involution | `def:commring-of-ai` | `HeckeRing.instCommRing_of_antiInvolution` | Comm 488 |
| transpose anti-involution | `def:gl-pair-ai` | `HeckeRing.GLn.GL_pair_antiInvolution` | Transpose 77 |
| transpose fixes every `HgH` | `lem:gl-pair-fix` | `HeckeRing.GLn.GL_pair_onHeckeCoset_eq` | Transpose 84 |
| GLₙ Hecke algebra commutative | `thm:commring-hecke-algebra` | `HeckeRing.GLn.instCommRing_HeckeAlgebra` | Transpose 98 |

### Ch.5 `05_gl2_operators.tex` — `GLn/Basic.lean`, `GLn/DiagonalCosets.lean`, `GL2/Basic.lean`
| Math object | label | `\lean{}` name | line/file |
|---|---|---|---|
| the arithmetic Hecke pair | `def:GL-pair` | `HeckeRing.GLn.GL_pair` | GLn/Basic 384 |
| GLₙ Hecke algebra | `def:hecke-algebra` | `HeckeRing.GLn.HeckeAlgebra` | GLn/Basic 397 |
| diagonal double coset | `def:T-diag` | `HeckeRing.GLn.T_diag` | DiagonalCosets 143 |
| diagonal basis element | `def:T-elem` | `HeckeRing.GLn.T_elem` | DiagonalCosets 147 |
| `T(a,d)` | `def:T-ad` | `HeckeRing.GL2.T_ad` | GL2/Basic 33 |
| `T(p,p)` | `def:T-pp` | `HeckeRing.GL2.T_pp` | GL2/Basic 46 |
| `T(m)=Σ T(a,m/a)` | `def:T-sum` | `HeckeRing.GL2.T_sum` | GL2/Basic 68 |
| `T(p)=T(1,p)` | `lem:T-sum-prime` | `HeckeRing.GL2.T_sum_prime` | GL2/Basic 85 |
| `T(1,1)=1` | `lem:T-ad-one-one` | `HeckeRing.GL2.T_ad_one_one` | GL2/Basic 62 |

### Ch.6 `06_multiplication_table.tex` — `GL2/MultiplicationTable.lean` + `GL2/Degree.lean`
| Math object | label | `\lean{}` name | line/file |
|---|---|---|---|
| `T(1)=1` (identity 1) | `lem:T-sum-one` | `HeckeRing.GL2.T_sum_one` | MultTable 551 |
| 3.24(2) telescoping | `thm:T-ad-one-ppow-eq` | `HeckeRing.GL2.T_ad_one_ppow_eq` | MultTable 94 |
| key prime computation | `thm:T-sum-prime-mul-T-ad` | `HeckeRing.GL2.T_sum_prime_mul_T_ad` | MultTable 512 |
| prime-power recurrence | `thm:T-sum-ppow-recurrence` | `HeckeRing.GL2.T_sum_ppow_recurrence` | MultTable 634 |
| 3.24(3) prime-power product | `thm:T-sum-ppow-mul` | `HeckeRing.GL2.T_sum_ppow_mul` | MultTable 847 |
| coprime multiplicativity | `thm:T-sum-mul-coprime` | `HeckeRing.GL2.T_sum_mul_coprime` | MultTable 928 |
| 3.24 full product | `thm:T-sum-mul` | `HeckeRing.GL2.T_sum_mul` | MultTable 1152 |
| 3.24(7) deg `T(pᵏ)` | `thm:deg-T-sum-prime-pow` | `HeckeRing.GL2.deg_T_sum_prime_pow` | Degree 122 |
| 3.24(6) deg `T(m)` | `thm:deg-T-sum` | `HeckeRing.GL2.deg_T_sum` | Degree 171 |

### Ch.7 `07_strong_multiplicity_one.tex` — `Newforms/Basic.lean`, `Newforms/MainLemma.lean`, `GL2/Gamma1Pair.lean`, `SMOObligations/StrongMultiplicityOneFull.lean`
| Math object | label | `\lean{}` name | line/file |
|---|---|---|---|
| Nebentypus space `S_k(N,χ)` | `def:modFormCharSpace` | `HeckeRing.GL2.modFormCharSpace` | Gamma1Pair 446 |
| eigenform | `def:eigenform` | `HeckeRing.GL2.Eigenform` | Newforms/Basic 49 |
| old subspace | `def:cuspFormsOld` | `HeckeRing.GL2.cuspFormsOld` | Newforms/Basic 158 |
| new subspace | `def:cuspFormsNew` | `HeckeRing.GL2.cuspFormsNew` | Newforms/Basic 207 |
| old part projection | `def:oldPart` | `HeckeRing.GL2.oldPart` | Newforms/Basic 390 |
| new part projection | `def:newPart` | `HeckeRing.GL2.newPart` | Newforms/Basic 395 |
| newform | `def:newform` | `HeckeRing.GL2.Newform` | Newforms/MainLemma 164 |
| 4.5.15(1) `aₙ=a₁λₙ` | `thm:coeff-eq-a1-lambda` | `HeckeRing.GL2.Eigenform.coeff_eq_coeff_one_mul_eigenvalue` | StrongMult 99 |
| 4.6.11 `a₁≠0` | `thm:a1-ne-zero` | `HeckeRing.GL2.coeff_one_ne_zero_of_mem_cuspFormsNew_of_eigen_unconditional` | StrongMult 175 |
| eigenform old/new split | `thm:eigenform-decomp` | `HeckeRing.GL2.exists_eigenform_decomposition_mem_cuspFormsNew` | StrongMult 276 |
| new part is a multiple of `f` | `thm:newPart-eq-smul` | `HeckeRing.GL2.newPart_eq_smul_of_shared_eigenvalues` | StrongMult 1103 |
| old part vanishes | `thm:oldPart-eq-zero` | `HeckeRing.GL2.oldPart_eq_zero_of_shared_eigenvalues` | StrongMult 1274 |
| **4.6.12 (headline)** | `thm:smo-constMul` | `HeckeRing.GL2.strongMultiplicityOne_constMul` | StrongMult 1382 |
| DS 5.8.2.1 corollary | `thm:smo-clean` | `HeckeRing.GL2.strongMultiplicityOne_axiom_clean_unconditional` | StrongMult 1419 |

## High-priority unformalisation sources

1. `.mathlib-quality/decomposition.md` — for **Chapter 7 only**: contains *verbatim*
   Miyake quotes (Thm 4.6.12 p.163, Lemma 4.5.15(1) p.149, Lemma 4.6.11 p.163, Lemma 4.6.2
   p.157, Lemma 4.6.9 p.162) and a Lean↔source match paragraph per leaf. Use it to write
   faithful proof sketches; cite as "[Miy, Thm 4.6.12]" etc.
2. Module docstrings (the `/-! # … -/` blocks) — each cited file's docstring carries the
   project-preferred prose statement and the Shimura/Miyake/DS reference. Mirror them.
3. Inline declaration docstrings — per-decl prose, usually already mathematical.

## References (for `\uses`-free prose citations)

- **[Sh]** G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*,
  Princeton, 1971 — §3.1–3.2 (Hecke rings, Prop 3.2, commutativity via transpose),
  Theorem 3.24 (the multiplication table). Chapters 1–6.
- **[Miy]** T. Miyake, *Modular Forms*, 2nd ed., Springer SMM, 2006 — §4.5–4.6, esp.
  Theorem 4.6.12, Lemmas 4.5.15, 4.6.8–4.6.11. Chapter 7.
- **[DS]** F. Diamond, J. Shurman, *A First Course in Modular Forms*, GTM 228, 2005 —
  §5.3 (Hecke operators), §5.5–5.8 (new/old, multiplicity one). Definitions in Chapters 5, 7.

## Per-worker contract (every chapter worker MUST follow)

1. Author **one** `\begin{theorem}`/`\begin{definition}`/`\begin{lemma}` block **per row**
   of your chapter's table above — no skipping, no merging. Use `\begin{definition}` for
   `def:` rows, `\begin{lemma}` for `lem:`, `\begin{theorem}` for `thm:`. Order the blocks
   so dependencies precede dependents (the table is already roughly topologically sorted).
2. Each block carries, in order: the chosen `\label{...}` (from the map), `\lean{Exact.Name}`
   (verified against the file's namespace), `\uses{...}` (all dependency labels — within
   and across chapters, from the global map), and `\leanok` (ALL entries — every file is
   sorry-free).
3. For non-trivial results add a `\begin{proof}` with `\uses{...}` + `\leanok` and a
   1–2 paragraph **mathematical** sketch (strategy, not tactics). For plain definitions,
   no proof block. For one-line/definitional lemmas, `\leanok` on the statement suffices.
4. Convert to the notation above; never leak Lean identifiers into theorem bodies.
5. Begin the chapter file with `\chapter{<Title>}\label{chap:<n>}` (documentclass is
   `report`). Append nothing else; the main agent wires `\input{}` into `content.tex`.
