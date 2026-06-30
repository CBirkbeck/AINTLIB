# Decomposition: Miyake Theorem 4.6.12 (Strong Multiplicity One, full constant-multiple form)

*Produced by `/develop` Phase 1e, 2026-05-26. Branch `hecke-ring`.*

## Skeleton location

The Lean skeleton (every lemma stated `:= by sorry`) lives in:

- `LeanModularForms/SMOObligations/StrongMultiplicityOneFull.lean`
  (`import LeanModularForms.SMOObligations`; namespace `HeckeRing.GL2`)

Elaboration verified with `lake env lean LeanModularForms/SMOObligations/StrongMultiplicityOneFull.lean`
at 2026-05-26: output is **only** `sorry` warnings (12) plus one `unused variable χ`
linter note on `cuspFormsOldChar_le_cuspFormsOld` (the χ parameter documents intent
but is not referenced by the current `cuspFormsOldChar` body — see gap #4). No type
errors; the full dependency shape type-checks.

> NOTE: a full `lake build` was deliberately **not** run — sibling files under
> `SMOObligations/` and `HeckeRIngs/GL2/Newforms/` are being edited concurrently by other
> workers, and `lake env lean` on this single file confirms the import shape independently.

## Source

- **[Miy]** T. Miyake, *Modular Forms*, 2nd ed., Springer SMM, 2006.
  Statement: §4.6, Theorem 4.6.12, **book p. 163** (= PDF p. 172 of `docs/Toshitsune Miyake.pdf`;
  PDF page = book page + 9).
  Proof: **book pp. 163–164** (PDF pp. 172–173).
  Supporting lemmas: 4.5.15 (book p. 149), 4.6.2 (book p. 157), Theorem 4.6.8 (book pp. 159–162),
  Lemma 4.6.9 (book p. 162), Lemma 4.6.10 (book p. 163), Lemma 4.6.11 (book p. 163).

## Result: `strongMultiplicityOne_constMul`

### Plain-English proof (Miyake pp. 163–164, transcribed)

Statement (verbatim, p. 163):

> "**Theorem 4.6.12.** Let f(z) and g(z) be elements of S_k^♯(N, χ) and S_k(N, χ),
> respectively. If f(z) and g(z) are common eigenfunctions of T(n) with the same
> eigenvalue for each n prime to some integer L, then g(z) is a constant multiple of f(z)."

Proof (verbatim, pp. 163–164):

> "Let f(z) = Σ_{n=1} aₙ e^{2πinz} be the Fourier expansion. Since a₁ ≠ 0 by Lemma 4.6.11,
> we may assume a₁ = 1. Furthermore we may assume N | L. Put
> g(z) = g⁽¹⁾(z) + g⁽²⁾(z)  (g⁽¹⁾(z) ∈ S_k^♯(N, χ), g⁽²⁾(z) ∈ S_k^♭(N, χ)).
> By Lemma 4.6.10, both g⁽¹⁾(z) and g⁽²⁾(z) are common eigenfunctions of T(n) with the
> same eigenvalue aₙ for each n prime to L. Assume g⁽¹⁾(z) ≠ 0, and put g⁽¹⁾(z) = Σ_{n=1} bₙ e^{2πinz}.
> By Lemma 4.6.11, we have b₁ ≠ 0. Let us show g⁽¹⁾(z) = b₁ f(z). We put
> g⁽¹⁾(z) − b₁ f(z) = Σ_{n=1} cₙ e^{2πinz}.
> Since b₁ aₙ = bₙ for all n prime to L by Lemma 4.5.15(1), we get cₙ = 0 for all n such that
> (n, L) = 1. Applying Theorem 4.6.8, we see g⁽¹⁾(z) − b₁ f(z) ∈ S_k^♭(N, χ), and g⁽¹⁾(z) = b₁ f(z).
> Next we shall prove that g⁽²⁾(z) = 0. First suppose N = m_χ, where m_χ is the conductor of χ.
> Then S_k^♭(N, χ) = 0. In particular, g⁽²⁾(z) = 0. Next assume N ≠ m_χ. We separate the proof
> into two steps.
> (i) If g⁽²⁾(z) ≠ 0, then there exist a proper divisor M of N satisfying m_χ | M, and a non-zero
> element h(z) of S_k^♯(M, χ) such that h | T(n) = aₙ h for all n prime to L. In fact, by definition,
> we may write g⁽²⁾(z) = Σ_v h_v(l_v z), (h_v(z) ∈ S_k^♯(M_v, χ), m_χ | M_v | N, M_v ≠ N). Since M_v
> divides N, Lemma 4.6.10 implies that S_k^♯(M_v, χ) has a basis consisting of eigenfunctions of T(n)
> for all n prime to L, so we may assume that all h_v(z) are common eigenfunctions of T(n) for all n
> prime to L. Lemma 4.6.2 implies that h_v(lz) are also common eigenfunctions of T(n) for all n prime
> to L. Since eigenfunctions with distinct eigenvalues are linearly independent, the summation on all
> h_v(l_v z) whose eigenvalues for T(n) are different from aₙ must vanish. Therefore, by removing such
> functions we may assume that all h_v(z) appearing on the right-hand side ... satisfy h_v | T(n) = aₙ h_v
> ((n, L) = 1). Therefore we may take any h_v(z) and M_v as h(z) and M, respectively.
> (ii) Let h(z) = c₁' e^{2πiz} + ⋯ be the element of S_k^♯(M, χ) obtained in (i). Since h | T(n) = aₙ h
> for all n prime to L, we see c₁' ≠ 0 by Lemma 4.6.11. Put h(z) − c₁' f(z) = Σ_{n=1} dₙ e^{2πinz}.
> Then by Lemma 4.5.15(1) dₙ = 0 if (n, L) = 1, and by Theorem 4.6.8 h(z) − c₁' f(z) ∈ S_k^♭(N, χ).
> Therefore f(z) = −c₁'⁻¹(h(z) − c₁' f(z)) + c₁'⁻¹ h(z) ∈ S_k^♭(N, χ); this contradicts the fact that
> f(z) is a nonzero element of S_k^♯(N, χ). Consequently we obtain g⁽²⁾(z) = 0, and therefore,
> g(z) = g⁽¹⁾(z) = b₁ f(z). □"

### Lean ↔ source match (top level)

`strongMultiplicityOne_constMul` takes `f : Newform N k` (Miyake's `f ∈ S_k^♯(N,χ)`,
normalised so `a₁ = 1` — the `Newform.isNorm` field), `g : Eigenform N k` (Miyake's
`g ∈ S_k(N,χ)`, a common eigenfunction with no normalisation), the shared-eigenvalue
hypothesis off a finite set `S` (Miyake's "prime to some integer L"; `Finset S`
generalises the divisors-of-`L` set, matching the existing `strongMultiplicityOne_axiom_clean`
interface), and the route-B `h_chi_factor` hypothesis (Miyake's character-conductor
restriction p. 160, inherited from the sorry-free Main Lemma). Conclusion `∃ c, g = c • f`
is Miyake's "g is a constant multiple of f"; the witness is `c = a₁(g) = b₁`.

The internal-node structure mirrors the source's two halves exactly:
the new-part identity `g⁽¹⁾ = b₁ f` (`newPart_eq_smul_of_shared_eigenvalues`) and the
old-part vanishing `g⁽²⁾ = 0` (`oldPart_eq_zero_of_shared_eigenvalues`), composed via
the project's `oldPart`/`newPart` decomposition.

---

## Decomposition tree

### Internal node R = `strongMultiplicityOne_constMul`

Source proof: Miyake pp. 163–164 (transcribed above). The source proves R by:
decompose `g = g⁽¹⁾ + g⁽²⁾`; show `g⁽¹⁾ = b₁ f`; show `g⁽²⁾ = 0`; conclude. Mirrored by:

- **L7** (`strongMultiplicityOne_constMul`) — assembly. Internal.
  - children: L5 (new part), L6 (old part = 0), plus the project's existing
    `oldPart_add_newPart`, `oldPart`/`newPart` membership API.

**Attacks (internal node R).** Could L5 and L6 both hold yet R fail?
- Composition: `g = newPart g + oldPart g` (`oldPart_add_newPart`, verified sorry-free
  `Newforms/Basic.lean:383`). L5 gives `newPart g = b₁ • f`; L6 gives `oldPart g = 0`
  (after wrapping `oldPart g ∈ cuspFormsOldChar`, which is the gap — see L6 risk). So
  `g = b₁ • f`, `c := b₁`. No composition gap *provided* `oldPart g` is shown to lie in
  `cuspFormsOldChar` (not merely `cuspFormsOld`). **This is the live composition risk**:
  the project's `oldPart g ∈ cuspFormsOld` (character-agnostic) but L6 is stated for
  `cuspFormsOldChar`. Resolving it needs `oldPart g ∈ cuspFormsOldChar` — i.e. the
  *reverse* of the gap-#4 bridge, which is the hard direction. **Flagged: R's composition
  depends on gap #4 in the hard direction unless restructured** (see Risk section / ticket T012).
- Edge `g = 0`: then `a₁(g)=0`, `c = 0`, `g = 0 • f = 0`. Holds.
- Edge `f = g` already equal: `c = 1`. Holds.
- Verdict: SURVIVES as stated *only modulo* the gap-#4 hard direction in the
  composition; this is the dominant project risk and is recorded as such.

---

### L1 (leaf, gap #1 — assembly from mathlib + project) — `Eigenform.coeff_eq_coeff_one_mul_eigenvalue`

Miyake Lemma 4.5.15(1), un-normalised form.

- Lean declaration: `StrongMultiplicityOneFull.lean:74`
- Source: Miyake §4.5, Lemma 4.5.15(1), book p. 149.
- Source claim (verbatim, p. 149, Lemma 4.5.15(1)): the eigenform relation between
  Fourier coefficients and Hecke eigenvalues,
  > "(1) aₙ = a₁ λₙ  (for the eigenvalue λₙ of T(n))."
  (Miyake states 4.5.15 for an eigenform `f = Σ aₙ qⁿ` with `T(n)f = λₙ f`; part (1) is
  `aₙ = a₁ λₙ`.)
- Lean ↔ source match: `(qExpansion 1 g).coeff n = (qExpansion 1 g).coeff 1 * g.eigenvalue n`
  for `(n,N)=1`. `g.eigenvalue n` is the project's classical Hecke eigenvalue `λₙ`
  (`Eigenform.eigenvalue`, with the diamond rescaling baked in so `T_n g = (eigenvalue n) • g`
  by `Eigenform.isEigen`). `(qExpansion 1 g).coeff 1` is `a₁`, `.coeff n` is `aₙ`.
- Discharged by (composition, project + mathlib):
  - `fourierCoeff_heckeT_n_period_one` (`HeckeRIngs/GL2/FourierHecke.lean:864`, **verified
    sorry-free**) at `m = 1`: `a₁(T_n g) = Σ_{d | gcd(1,n)} … = a₁(g)·`(d=1 term) `= aₙ(g)`
    since `gcd(1,n)=1` collapses the sum to `d=1`.
  - `Eigenform.isEigen` (`Newforms/Basic.lean:76`, sorry-free): `T_n g = (eigenvalue n) • g`,
    so `a₁(T_n g) = (eigenvalue n)·a₁(g)` via `qExpansion_smul`.
  - Equate: `aₙ(g) = a₁(g)·(eigenvalue n)`. (≤ 3 project lemmas + `qExpansion_smul`.)
  - Pattern model: `eigenvalue_eq_fourierCoeff_one` (`FourierHecke.lean:912`) does the
    `a₁=1` case by exactly this route; L1 drops the `a₁=1` simplification.
- **Attacks attempted:**
  - [1] Counterexample search: `aₙ = a₁ λₙ` is the defining eigenform relation; no
    contradicting lemma in project (`grep` over `Newforms/` finds only the `a₁=1`
    specialisation `eigenvalue_eq_fourierCoeff_one`, which agrees). No mathlib negation.
  - [2] Edge cases: `n = 1`: gives `a₁ = a₁·λ₁` with `λ₁ = 1` (`heckeT_n` at `n=1` is the
    identity, `eigenvalue ⟨1,_⟩ = χ(1)·ring = 1`); holds. `a₁(g) = 0`: gives `aₙ = 0`,
    consistent (this is precisely the hypothesis used in L2/4.6.11).
  - [3] Hypothesis test: `(n,N)=1` necessary — `fourierCoeff_heckeT_n_period_one` requires
    coprimality (the `χ`-multiplicativity uses `ZMod.unitOfCoprime`); dropping it breaks the
    `d=1`-collapse. χ-membership `hgχ` necessary: the building block is stated for forms in
    a single Nebentypus eigenspace. No hidden assumption beyond these.
  - [4] Source-drift: re-read p. 149 — 4.5.15(1) is exactly `aₙ = a₁ λₙ`. Lean matches
    (the `eigenvalue` carries the classical normalisation via `isEigen`). No drift.
  - [5] Discharge attack: `lean_local_search`/`Read` confirm `fourierCoeff_heckeT_n_period_one`
    type at `FourierHecke.lean:864` matches (returns the gcd-sum; at `m=1` divisors of
    `gcd(1,n)=1` give the singleton `{1}`). `Eigenform.isEigen` at `Newforms/Basic.lean:76`
    matches. Composition is 3 lemmas (≤ 3 ✓). Both project decls sorry-free.
  - Verdict: SURVIVED. Buildable assembly; ~40 LOC (model `eigenvalue_eq_fourierCoeff_one`
    is ~15 lines, L1 adds the un-normalised bookkeeping).
- Prior-B2 log: `b2_log.jsonl` absent (no `/beastmode` B2 history). No name/shape match.

### L2 (leaf, gap #2 — assembly) — `coeff_one_ne_zero_of_mem_cuspFormsNew_of_eigen`

Miyake Lemma 4.6.11.

- Lean declaration: `StrongMultiplicityOneFull.lean:93`
- Source: Miyake §4.6, Lemma 4.6.11, book p. 163.
- Source claim (verbatim, p. 163):
  > "**Lemma 4.6.11.** Let f(z) = Σ_{n=1} aₙ e^{2πinz} be an element of S_k^♯(N, χ). If f(z)
  > is a common eigenfunction of Hecke operators T(n) for all n prime to some integer L,
  > then a₁ ≠ 0.
  > *Proof.* Assume a₁ = 0. Then by Lemma 4.5.15(1), we see aₙ = 0 for all n prime to L.
  > Therefore f(z) ∈ S_k^♭(N, χ) by Theorem 4.6.8, which is a contradiction. □"
- Lean ↔ source match: `(qExpansion 1 g).coeff 1 ≠ 0` for `g` a nonzero `Eigenform` in
  `cuspFormsNew N k ∩ modFormCharSpace χ`. The `L`, `hNL : N ∣ L`, and `S`(implicit via
  the eigenvalue source) match "prime to some integer L"; we use `N ∣ L` so "prime to L"
  ⟹ "prime to N" (where 4.5.15(1) applies).
- Discharged by (composition, project):
  - Contrapositive: assume `a₁(g) = 0`. By **L1** (`Eigenform.coeff_eq_coeff_one_mul_eigenvalue`),
    `aₙ(g) = a₁(g)·λₙ = 0` for all `(n,N)=1`.
  - `mainLemma_charSpace_routeB` (`SMOObligations.lean:232`, **verified sorry-free**,
    needs `h_chi_factor`): vanishing coprime coefficients ⟹ `g ∈ cuspFormsOld N k`.
  - `cuspFormsOld_disjoint_cuspFormsNew` (`Newforms/Basic.lean:196`, sorry-free) +
    `petN_definite`: `g ∈ old ∩ new ⟹ g = 0`, contradicting `hg_ne`.
- **Attacks attempted:**
  - [1] Counterexample: would need a nonzero new eigenform with `a₁=0`. Theorem 4.6.8
    (route B) forbids exactly this. No project lemma asserts existence of such a form.
  - [2] Edge cases: `g = 0` excluded by `hg_ne`. `N = 1`: `cuspFormsOld 1 k` is spanned by
    levelRaise from proper divisors of 1 = ∅, so `= ⊥`; then new = everything, and a
    nonzero form has `a₁ ≠ 0` iff … — actually at `N=1` Miyake's claim still needs 4.6.8;
    route B applies (vacuous `h_chi_factor` since `primeFactors 1 = ∅`). Holds.
  - [3] Hypothesis test: `hg_new` necessary (an old form CAN have `a₁=0`, e.g. a level-raise
    `V_p h` has `a₁ = 0`); this is the whole point. `h_chi_factor` necessary for route B
    (the bare `mainLemma` is sorry'd, `MainLemma.lean:428`). `hgχ` necessary (route B is
    per-character).
  - [4] Source-drift: p. 163 says "f ∈ S_k^♯(N,χ)" (new) and concludes `a₁ ≠ 0`. Lean matches.
    Miyake's proof uses 4.5.15(1) then 4.6.8 then new∩old=0 — Lean mirrors exactly (L1 +
    route-B 4.6.8 + disjointness). No drift.
  - [5] Discharge attack: `mainLemma_charSpace_routeB` signature read at `SMOObligations.lean:232`
    — takes `χ`, `f ∈ cuspFormCharSpace`, `h_vanish`, `h_chi_factor`, concludes `f ∈ cuspFormsOld`.
    Matches. `cuspFormsOld_disjoint_cuspFormsNew` read at `Newforms/Basic.lean:196`. Both
    sorry-free. Need a `cuspFormCharSpace`↔`modFormCharSpace` bridge
    (`cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace`, used in
    `newform_unique_routeB`) — 1 extra lemma, total ≤ 4; acceptable for an internal-ish leaf.
  - Verdict: SURVIVED. Buildable; ~50 LOC (mirrors `newform_unique_routeB`'s vanishing
    machinery, ~30 lines, plus the contrapositive wrapper).
- Prior-B2 log: no history file; no match.

### L3 (leaf, gap #3 — eigenvalue corollary of existing commutation) — `heckeT_n_levelRaise_eigen`

Miyake Lemma 4.6.2 (eigenvalue-preservation form).

- Lean declaration: `StrongMultiplicityOneFull.lean:121`
- Source: Miyake §4.6, Lemma 4.6.2, book p. 157.
- Source claim (verbatim, p. 157, Lemma 4.6.2):
  > "**Lemma 4.6.2.** … (V_l f) | T(n) = (f | T(n))(lz) for (n, lN) = 1 …"
  (Miyake's Lemma 4.6.2 establishes that `f ↦ f(lz)` commutes with `T(n)` for `(n, lN)=1`,
  whence common eigenfunctions map to common eigenfunctions with the same eigenvalues.)
- Lean ↔ source match: `heckeT_n_cusp k n (V_l h) = lam • (V_l h)` given
  `heckeT_n_cusp k n h = lam • h`, where `V_l = levelRaise M l k` and `(n,N)=1`,
  `N = l*M`. The eigenvalue `lam` is preserved.
- Discharged by (composition, project):
  - `heckeT_n_levelRaise_comm` (`Newforms/LevelRaiseComm.lean:883`, **verified sorry-free**):
    `T_n (V_l h) = V_l (T_n h)` for `(n, l*M) = 1`.
  - Substitute `T_n h = lam • h`, then `V_l (lam • h) = lam • V_l h` by `map_smul`
    (`levelRaise` is `→ₗ[ℂ]`). (2 lemmas, ≤ 3 ✓.)
- **Attacks attempted:**
  - [1] Counterexample: `levelRaise` is a `LinearMap` (`Newforms/Basic.lean:125` usage,
    def `LevelRaise.lean:231`), so `map_smul` is forced; commutation is the cited theorem.
    No contradiction possible.
  - [2] Edge cases: `lam = 0`: `T_n(V_l h) = V_l 0 = 0 = 0 • V_l h`. Holds. `l = 1`:
    `V_1 = ` levelRaise by 1 (identity up to the project's `1-k` scaling); commutation
    still holds. `h = 0`: trivial.
  - [3] Hypothesis test: `(n,N)=1` necessary (commutation theorem requires `Coprime n (l*M)`
    and `N = l*M`). The coprimality is exactly Miyake's `(n,lN)=1` after `N ← l*M`.
  - [4] Source-drift: p. 157 gives the commutation; the eigenvalue corollary is immediate
    and is exactly how Miyake uses it in 4.6.12(i) ("h_v(lz) are also common eigenfunctions").
    Lean states the corollary directly. No drift.
  - [5] Discharge attack: `heckeT_n_levelRaise_comm` read at `LevelRaiseComm.lean:883` —
    signature `heckeT_n_cusp k n (heq ▸ levelRaise M d k g) = heq ▸ levelRaise M d k (heckeT_n_cusp k n g)`
    for `Coprime n N`, `d*M=N`. Exact match (with `d ← l`). Sorry-free. `map_smul` is mathlib.
    Composition = 2 lemmas (✓). NOTE: the `heq ▸` transport must be handled; `subst heq`
    then `map_smul` — standard, no extra cost.
  - Verdict: SURVIVED. Buildable; ~20 LOC (commutation is one rewrite + `map_smul`).
- Prior-B2 log: no history file; no match.

### L4 = API GAP #4 (internal, RISKIEST) — the χ-refined old space `S_k^♭(N,χ)`

Miyake Lemma 4.6.9 (p. 162). **This subtree is the central risk.**

Source claim (verbatim, p. 162):

> "Hereafter we consider only cusp forms. We denote by S_k^♭(N, χ) the subspace of S_k(N, χ)
> generated by the set ⋃_M ⋃_l {f(lz) | f(z) ∈ S_k^♯(M, χ)}. Here M runs over all positive
> integers such that m_χ | M, M | N, and M ≠ N; l runs over all positive divisors of N/M
> (including both 1 and N/M); m_χ is the conductor of χ. In other words, S_k^♭(N, χ) is the
> subspace of S_k(N, χ) generated by cusp forms essentially of lower levels. Furthermore, we
> denote by S_k^♯(N, χ) the orthocomplement of S_k^♭(N, χ) in S_k(N, χ) with respect to the
> Petersson inner product. Namely, S_k^♯(N, χ) = S_k^♭(N, χ)⊥. …
> **Lemma 4.6.9.** (1) If χ is a primitive Dirichlet character of conductor N, then
> S_k^♯(N, χ) = S_k(N, χ). (2) If m_χ | M, M | N and M ≠ N, then S_k^♯(M, χ) ⊆ S_k^♭(N, χ).
> (3) S_k^♭(N, χ) is generated by the set ⋃_M ⋃_l {f(lz) | f(z) ∈ S_k^♯(M, χ)}. Here M runs
> over all positive integers such that m_χ | M and M | N; l runs over all positive divisors
> of N/M (including both 1 and N/M)."

**The mismatch (gap #4).** The project's `cuspFormsOld N k` (`Newforms/Basic.lean:131`) is
`Submodule.span ℂ {f | IsOldformGenerator f}` where a generator is `levelRaise M d k g`
for **any** `g : CuspForm (Gamma1 M)` (the *full* space) and **any** proper divisor `M`
(`d*M=N`, `1<d`), with **no** `m_χ | M` condition and **no** restriction to the new
subspace at level `M`. Miyake's `S_k^♭(N,χ)` uses the **new** spaces `S_k^♯(M,χ)` and
requires `m_χ | M`. These are genuinely different submodules in general (Miyake's is
smaller; equality is a theorem, not a definition — and 4.6.9(1) is precisely the
non-trivial collapse for primitive χ). The project's `docs/plans/strong-multiplicity-one.md`
(line 35, 617) *identifies* `cuspFormsOld` with Miyake's `S_k^♯`/`S_k^♭`, but that
identification is **not formalised** and is the crux of this gap.

The skeleton introduces a **new** definition `cuspFormsOldChar N k χ m_χ`
(`StrongMultiplicityOneFull.lean:152`) = Miyake's `S_k^♭` verbatim (span of `V_l`-images
of `cuspFormsNew M k` over `m_χ | M`, `M ≠ N`, `l*M = N`), and develops 4.6.9 against it.

> **CAVEAT recorded in skeleton:** `cuspFormsOldChar`'s body uses the project's
> `cuspFormsNew M k`, which is **character-agnostic** (the project never threads χ through
> the new space at level M). Miyake's `S_k^♯(M,χ)` is the χ-eigenspace of the new space.
> A fully faithful formalisation may need `cuspFormsNew M k ∩ cuspFormCharSpace_M χ_M` where
> `χ_M` is χ restricted mod M (valid because `m_χ | M`). This refinement is folded into the
> gap-#4 tickets (T006a) and is itself non-trivial (needs the conductor-descent
> `χ = χ_M ∘ (ZMod.unitsMap …)`, available via `DirichletCharacter.conductor` API).

Children of L4 (each its own ticket; ordered):

- **L4.0** (def) `cuspFormsOldChar` — `StrongMultiplicityOneFull.lean:152`. Definition + the
  basic span API (`mem`, `subset_span`, additivity). Source: p. 162 (verbatim above).
- **L4.1** (leaf-ish, build) `levelRaise_cuspFormsNew_le_cuspFormsOldChar` =
  **4.6.9(2)** — `StrongMultiplicityOneFull.lean:173`. Discharged by `Submodule.subset_span`
  once the generator membership is unfolded. Source p. 162. **Attacks:** edge `l=N/M` and
  `l=1` both allowed by Miyake ("including both 1 and N/M"); `M≠N` required (else not proper);
  the χ-eigenspace refinement (caveat) is the only subtlety. SURVIVES modulo the caveat.
- **L4.2** (leaf, RISKIEST sub-leaf) `cuspFormsOldChar_eq_bot_of_conductor_eq` =
  **4.6.9(1)** — `StrongMultiplicityOneFull.lean:193`. Source p. 162: "If χ is primitive of
  conductor N, then S_k^♯ = S_k, [so S_k^♭ = 0]." **This is the hardest leaf.** When
  `m_χ = N`, the index set `{M : m_χ | M ∣ N, M ≠ N}` is **empty** (the only multiple of `N`
  dividing `N` is `N` itself, which is excluded by `M ≠ N`), so the span is over the empty
  generator set ⟹ `⊥`. **So with the `cuspFormsOldChar` definition above, 4.6.9(1) is a
  combinatorial triviality** (`Nat.dvd` + `M ≠ N` ⟹ no `M`), NOT the deep statement Miyake
  proves. The depth in Miyake comes from `S_k^♯ = (S_k^♭)⊥ = S_k`; but as a statement
  *about the generated `S_k^♭`* it is empty-index-set ⟹ ⊥. **Attacks:**
  - [counterexample] Is there `M` with `m_χ = N ∣ M ∣ N`, `M ≠ N`? `N ∣ M ∧ M ∣ N ⟹ M = N`
    (`Nat.dvd_antisymm`), contradicting `M ≠ N`. So index set empty. No counterexample.
  - [edge] `N = 1`: `m_χ = 1`, but `M ∣ 1 ⟹ M = 1 = N`, excluded — empty. ⊥. Holds.
  - [drift] Miyake's `m_χ = N` ⟺ `χ` primitive (conductor = level). The Lean hyp
    `χ.conductor = N` is exactly `m_χ = N`. We bind `m_χ := χ.conductor`. Match.
  - Verdict: SURVIVES, and is *easy* under the chosen definition. (The "risk" was that
    4.6.9(1) is deep; under the span-definition it is not — the depth is hidden in the
    equivalence `cuspFormsOldChar = cuspFormsOld`, which 4.6.12 does NOT require. See Risk.)
  - **~10 LOC** (`Submodule.span_empty`-style + `Nat.dvd_antisymm`).
- **L4.3** (internal, build) `exists_levelRaise_eigen_decomposition_of_mem_cuspFormsOldChar`
  = **4.6.9(3) + eigen-refinement** — `StrongMultiplicityOneFull.lean:207`. Source p. 162
  (generation) + p. 164 (i) (replace each `h_v` by an eigenbasis). Discharged by
  `Submodule.span_induction` over `cuspFormsOldChar` generators, then `Lemma 4.6.10`
  (`heckeT_n_preserves_cuspFormsNew`, **verified sorry-free** `LevelRaiseComm.lean:966`)
  to pick eigen-components, then `L3` (4.6.2) to push eigenvalues through `V_l`.
  **Attacks:** the eigenbasis existence at level `M` uses the joint-eigenspace
  decomposition `heckeFamily_directSum_isInternal` (`AdjointTheoryPetersson.lean:790`,
  sorry-free but `private` — needs a public restatement, T011). Composition is multi-step
  ⟹ genuinely internal, not a single discharge. **~120 LOC** (Miyake's (i) is ~12 source
  lines but the eigenbasis + linear-independence bookkeeping is heavy in Lean).
- **L4.4** (leaf, build) `cuspFormsOldChar_le_cuspFormsOld` — gap-#4 **bridge (easy
  direction)** — `StrongMultiplicityOneFull.lean:227`. Every Miyake-generator
  `V_l g` with `g ∈ cuspFormsNew M k` is also a project-generator (`g ∈ S_k(Γ₁(M))`,
  `M` proper divisor), so lies in `cuspFormsOld N k`. Discharged by `Submodule.span_mono`
  / `span_le` + `Submodule.subset_span ⟨M, l, …, rfl⟩`. **Attacks:** need `1 < l`
  (project requires `1 < d`); Miyake allows `l = 1` for `M ≠ N`. **EDGE CASE FLAG**: when
  `l = 1` (so `M = N`), Miyake excludes it (`M ≠ N`); when `l = 1` is allowed by Miyake's
  4.6.9(3) it forces `M = N` which the index excludes — so on `cuspFormsOldChar`'s index
  (`M ≠ N` ⟹ `l ≥ 2`) we always have `1 < l`. Need to verify `M ≠ N ∧ l*M = N ⟹ 1 < l`
  (`l = 1 ⟹ M = N`, contradiction; `l = 0 ⟹ N = 0`, excluded by `NeZero N`). SURVIVES.
  **~25 LOC.**

**L4 internal-node attack (composition).** Does 4.6.12 actually only need
{L4.1, L4.2, L4.3, L4.4} and never the *reverse* inclusion `cuspFormsOld ≤ cuspFormsOldChar`?
- The new-part argument (L5) needs: `g_new - b₁ f ∈ cuspFormsOld` (from route-B 4.6.8) **and**
  `∈ cuspFormsNew`, then disjointness. This uses only `cuspFormsOld`, **not** `cuspFormsOldChar`.
- The old-part argument (L6) is stated with `g_old ∈ cuspFormsOldChar`; it descends via L4.3,
  normalises via L2, and derives the contradiction `f ∈ cuspFormsOld` (via L4.4 +
  route-B 4.6.8) vs `f` new. Uses L4.1–L4.4 forward only.
- **BUT** the *assembly* R needs to obtain `g_old ∈ cuspFormsOldChar` from `g`'s decomposition.
  The project's `oldPart g ∈ cuspFormsOld` (forward), and to feed L6 we need
  `oldPart g ∈ cuspFormsOldChar` — the **reverse** direction. **This is the open hard part.**
  - *Mitigation A (restructure, recommended):* decompose `g` directly in Miyake's
    `cuspFormsOldChar ⊕ cuspFormsNew` instead of the project's `cuspFormsOld ⊕ cuspFormsNew`.
    This needs `IsCompl (cuspFormsOldChar …) (cuspFormsNew …)` — a *new* decomposition theorem
    (the project only has `cuspFormsOld_isCompl_cuspFormsNew`). Proving it requires
    `cuspFormsNew = (cuspFormsOldChar)⊥` (Miyake's *definition* of `S_k^♯` as `(S_k^♭)⊥`),
    which the project does NOT match (the project defines `cuspFormsNew = (cuspFormsOld)⊥`).
    So Mitigation A reduces to: `(cuspFormsOldChar)⊥ = (cuspFormsOld)⊥` i.e.
    `cuspFormsOldChar` and `cuspFormsOld` have the **same orthocomplement** — equivalently
    (finite-dim, nondegenerate) the **same closure/span-saturation**. This is morally
    `cuspFormsOldChar = cuspFormsOld` after all, OR at least same `⊥`.
  - *Mitigation B (accept extra hypothesis):* state 4.6.12 with `g`'s old part *assumed* in
    `cuspFormsOldChar` (i.e. take `g ∈ cuspFormsOldChar ⊔ cuspFormsNew` as a hypothesis,
    matching the master plan's `hg1 : g ∈ … ⊔ …`). Then no reverse bridge is needed. This is
    **honest** and matches Miyake's framing (`g ∈ S_k(N,χ) = S_k^♭ ⊕ S_k^♯`), provided we
    also prove `S_k(N,χ) = cuspFormsOldChar ⊔ cuspFormsNew` — which is again the
    codisjointness gap.
- **Verdict (L4 / gap #4):** The forward leaves (L4.1–L4.4) are bounded and mostly easy.
  The **decomposition codisjointness** `S_k(N,χ) = cuspFormsOldChar ⊕ cuspFormsNew`
  (equivalently the reverse bridge / same-orthocomplement) is **the genuinely open,
  potentially open-ended sub-problem**. It is recorded as its own ticket (T012,
  RISKIEST) and feasibility is rated **MEDIUM-LOW** (see Risk section). All other leaves
  are feasible.

### L5 (internal, build — close to existing SMO) — `newPart_eq_smul_of_shared_eigenvalues`

Miyake 4.6.12 new part (p. 163).

- Lean declaration: `StrongMultiplicityOneFull.lean:259`
- Source claim (verbatim, p. 163, new part): see top-level transcription — "Assume g⁽¹⁾ ≠ 0
  … b₁ ≠ 0 … g⁽¹⁾ − b₁ f = Σ cₙ qⁿ … cₙ = 0 for (n,L)=1 … by Theorem 4.6.8 … ∈ S_k^♭ …
  and g⁽¹⁾ = b₁ f."
- Lean ↔ source match: `g_new = (a₁ g_new) • f` for `g_new` a new eigenform sharing `f`'s
  eigenvalues off `S`. The `b₁ = a₁(g_new) = (qExpansion 1 g_new).coeff 1`.
- Discharged by (composition, project + L1/L2): mirror `newform_unique_routeB`
  (`SMOObligations.lean:258`, sorry-free): set `h := g_new - b₁ • f`; show its coprime
  coefficients vanish using **L1** (`cₙ = bₙ - b₁ aₙ = b₁ aₙ - b₁ aₙ = 0` via `aₙ(g_new) =
  b₁ λₙ` and `aₙ(f) = λₙ` from `Newform.eigenvalue_eq_coeff`); apply route-B 4.6.8
  (`mainLemma_charSpace_routeB`) ⟹ `h ∈ cuspFormsOld`; `h ∈ cuspFormsNew` (both new);
  disjointness ⟹ `h = 0`. (`b₁ ≠ 0` from **L2** is needed only to *rule out the case
  analysis*; actually the identity `g_new = b₁ f` holds even if `b₁ = 0` ⟹ `g_new = 0` by
  L2's contrapositive, so the `b₁ ≠ 0` is consistency not necessity here.)
- **Attacks attempted:**
  - [1] Counterexample: `newform_unique_routeB` is the `b₁ = 1` shadow of this; no
    contradiction. The only freedom is the scalar `b₁`, fixed as `a₁(g_new)`.
  - [2] Edge: `g_new = 0` ⟹ `b₁ = 0` ⟹ `0 = 0 • f`. Holds. `g_new = f` (f as eigenform,
    `b₁ = 1`): `f = 1 • f`. Holds.
  - [3] Hypothesis test: `hg_new` necessary (the identity is false for old `g_new`).
    `h_chi_factor` necessary (route-B 4.6.8). Shared eigenvalues off `S` necessary (else
    `cₙ ≠ 0`). `f` `Newform` (normalised) necessary so `aₙ(f) = λₙ` (`eigenvalue_eq_coeff`).
  - [4] Source-drift: Lean's `S` (finite set) generalises Miyake's "primes dividing L";
    the existing `eigenvalues_eq_all_coprime_of_eq_off_finite` (`SMOObligations.lean:362`,
    sorry-free) already bridges "off finite S" to "all coprime", so the generalisation is
    sound and matches the SMO interface. No drift.
  - [5] Discharge attack: `newform_unique_routeB` read at `SMOObligations.lean:258` (sorry-free)
    is the exact template (`b₁=1`); reusing its body with `b₁` scalar = ~4 lemmas but it is
    an *internal* node (multi-step), correctly not a single-discharge leaf. `Newform.eigenvalue_eq_coeff`
    (`MainLemma.lean:256`, sorry-free) discharges `aₙ(f) = λₙ`. L1 discharges `aₙ(g_new)`.
  - Verdict: SURVIVED. Buildable, low risk; ~70 LOC (template `newform_unique_routeB` is
    ~45 lines; L5 adds the `b₁`-scalar bookkeeping).
- Prior-B2 log: no history; no match.

### L6 (internal, build — consumes gaps #3, #4) — `oldPart_eq_zero_of_shared_eigenvalues`

Miyake 4.6.12 steps (i)+(ii) (p. 164).

- Lean declaration: `StrongMultiplicityOneFull.lean:291`
- Source claim (verbatim, p. 164): see top-level transcription, steps (i) and (ii).
- Lean ↔ source match: `g_old = 0` for `g_old ∈ cuspFormsOldChar` a common eigenfunction
  sharing `f`'s eigenvalues off `S`, with `f` a nonzero newform. Mirrors "g⁽²⁾ = 0".
- Discharged by (composition): if `g_old ≠ 0`, apply **L4.3** (4.6.9(3) eigen-decomposition)
  to get a nonzero eigen-component `V_l h`, `h ∈ cuspFormsNew M k` eigenform at proper
  divisor `M`, with eigenvalue `aₙ` (drop others via **L_indep** = `petN_eq_zero_of_ne_eigenvalues`
  / linear independence). Then `h ≠ 0` ⟹ `c₁' = a₁(h) ≠ 0` (**L2** at level `M`). Set
  `h - c₁' • f`: coprime coeffs vanish (**L1** at level `M` + `eigenvalue_eq_coeff` for `f`);
  route-B 4.6.8 ⟹ `h - c₁' • f ∈ cuspFormsOld N k`; also `h ∈ cuspFormsOld N k` via **L4.1**
  (4.6.9(2)) + **L4.4** (bridge); so `f = c₁'⁻¹ h - c₁'⁻¹(h - c₁' f) ∈ cuspFormsOld N k`,
  contradicting `f` new (via `mem_cuspFormsNew_iff_oldPart_eq_zero` /
  `cuspFormsOld_disjoint_cuspFormsNew` with `f ≠ 0`).
- **Attacks attempted:**
  - [1] Counterexample: the contradiction is Miyake's; no project lemma asserts a nonzero
    new `f` lies in `cuspFormsOld`. The descent's nonzero component exists because
    `g_old ≠ 0` and the eigen-decomposition is faithful (L4.3).
  - [2] Edge: `g_old = 0` is the goal (trivial if assumed). `M = 1`: `h ∈ cuspFormsNew 1 k`;
    a level-1 new form with `c₁' ≠ 0`; still `h ∈ cuspFormsOld N k` via 4.6.9(2)
    (`m_χ | 1` forces `m_χ = 1`). Holds.
  - [3] Hypothesis test: `g_old ∈ cuspFormsOldChar` (not just `cuspFormsOld`) **necessary**
    for L4.3's descent (the descent is defined on `cuspFormsOldChar`). `f` nonzero new
    necessary for the final contradiction. `h_chi_factor` necessary (4.6.8). This is where
    the **gap-#4 dependency is real**: L6 is honestly stated on `cuspFormsOldChar`.
  - [4] Source-drift: Lean mirrors (i)+(ii) step by step. The one liberty: Miyake's
    `h | T(n) = aₙ h` becomes "∃ lam, T_n g_old = lam • g_old ⟹ f.eigenvalue n = lam" in
    the hypothesis `h_eig` — i.e. g_old's eigenvalue equals f's; faithful.
  - [5] Discharge attack: depends on L4.3 (internal, has own attack log), L1, L2, L4.1,
    L4.4, L_indep, route-B 4.6.8, disjointness. All cited decls verified to exist; the
    sorry'd ones (`mainLemma`, L-series) are NOT used (route B only). Multi-step ⟹ correctly
    internal.
  - Verdict: SURVIVED *as an internal node*, conditional on L4.3 and the gap-#4 forward
    leaves. Its own correctness does not need the reverse bridge (that risk lives in R's
    composition / T012). **~150 LOC** (Miyake's (i)+(ii) is ~22 source lines; heavy in Lean
    due to the descent + double 4.6.8 application).
- Prior-B2 log: no history; no match.

### L_indep (leaf, project — public restatement) — `petN_eq_zero_of_ne_eigenvalues`

"Eigenfunctions with distinct eigenvalues are linearly independent" (Miyake p. 164).

- Lean declaration: `StrongMultiplicityOneFull.lean:241`
- Source: Miyake p. 164 ("Since eigenfunctions with distinct eigenvalues are linearly
  independent …"). Standard linear algebra; Miyake uses it without proof.
- Lean ↔ source match: distinct `T_n`-eigenvalues ⟹ Petersson-orthogonal (`petN f g = 0`),
  which gives linear independence in the finite-dim space.
- Discharged by: **exact** copy of the **private** `eigenforms_orthogonal_of_ne_eigenvalues`
  (`AdjointTheoryPetersson.lean:810`, **verified sorry-free**). Action: make a public wrapper
  (the body is `refine eigenforms_orthogonal_of_distinct_eigenvalues …`). Since the source
  lemma is `private`, the wrapper must either (a) re-prove via the public
  `heckeT_n_adjoint_on_charSpace`, or (b) the original is de-privatised. **Recommend (b)**:
  drop `private` on `AdjointTheoryPetersson.lean:810` (1-line change, no logic touched).
- **Attacks attempted:**
  - [1] Counterexample: orthogonality of distinct-eigenvalue eigenvectors of a self-adjoint
    operator is standard; `heckeT_n_adjoint_on_charSpace` provides the (twisted) self-adjointness.
    No counterexample.
  - [2] Edge: `f = 0` or `g = 0` excluded by `hf_ne`/`hg_ne` (needed: orthogonality of 0 is
    trivial but the *proof* divides by `petN f f ≠ 0`). `a = b` excluded by `h_diff_ab`.
  - [3] Hypothesis test: `hf_ne`, `hg_ne` necessary (definiteness step). Same-χ necessary
    (adjoint formula is per-character). `(n,N)=1` necessary.
  - [4] Source-drift: Miyake says "linearly independent"; Lean proves the stronger
    "orthogonal" (⟹ independent in inner-product space). Slightly stronger, fine.
  - [5] Discharge attack: `eigenforms_orthogonal_of_ne_eigenvalues` read at
    `AdjointTheoryPetersson.lean:810`; signature **matches L_indep exactly** (same args).
    Sorry-free. Only obstacle: `private`. ≤ 1 lemma. ✓
  - Verdict: SURVIVED. Buildable; **~5 LOC** (wrapper) or 1-line de-privatise.
- Prior-B2 log: no history; no match.

---

## Summary of leaves

| Leaf | Miyake | Status | Discharge | Risk | ~LOC |
|------|--------|--------|-----------|------|------|
| L1 | 4.5.15(1) | BUILD (assembly) | `fourierCoeff_heckeT_n_period_one` + `Eigenform.isEigen` | low | 40 |
| L2 | 4.6.11 | BUILD (assembly) | L1 + `mainLemma_charSpace_routeB` + disjointness | low | 50 |
| L3 | 4.6.2 | BUILD (corollary) | `heckeT_n_levelRaise_comm` + `map_smul` | low | 20 |
| L4.0 | 4.6.9 def | BUILD (new def) | `Submodule.span` | low | 15 |
| L4.1 | 4.6.9(2) | BUILD | `Submodule.subset_span` | low-med | 30 |
| L4.2 | 4.6.9(1) | BUILD | empty index ⟹ `⊥` (`Nat.dvd_antisymm`) | low | 10 |
| L4.3 | 4.6.9(3)+(i) | BUILD (internal) | span-induction + 4.6.10 + L3 + eigenbasis | med | 120 |
| L4.4 | bridge (easy dir) | BUILD | `Submodule.span_mono` | low | 25 |
| L_indep | 4.6.12(i) | BUILD (de-privatise) | `eigenforms_orthogonal_of_ne_eigenvalues` | low | 5 |
| L5 | 4.6.12 new part | BUILD (internal) | template `newform_unique_routeB` + L1 + L2 | low | 70 |
| L6 | 4.6.12 (i)+(ii) | BUILD (internal) | L4.3 + L1 + L2 + L4.1 + L4.4 + L_indep + 4.6.8 | med | 150 |
| **T012** | decomp codisjoint | **OPEN/HARD** | `IsCompl (cuspFormsOldChar) (cuspFormsNew)` / same-⊥ | **MED-LOW** | 150–400+ |
| L7 | 4.6.12 assembly | BUILD (internal) | L5 + L6 + `oldPart_add_newPart` (+T012) | gated on T012 | 60 |

Existing infrastructure reused (verified sorry-free): `mainLemma_charSpace_routeB`,
`newform_unique_routeB`, `strongMultiplicityOne_axiom_clean`, `cuspFormsOld_isCompl_cuspFormsNew`,
`oldPart`/`newPart` + API, `heckeT_n_preserves_cuspFormsOld/New` (4.6.10),
`heckeT_n_levelRaise_comm`, `levelRaise` (V_l), `Newform.eigenvalue_eq_coeff`,
`Eigenform.isEigen`, `fourierCoeff_heckeT_n_period_one`, `Newform.eigenvalue_coprime_mul`,
`eigenforms_orthogonal_of_ne_eigenvalues` (private), `DirichletCharacter.conductor`.

Avoided sorries (NOT on critical path): `mainLemma` (`MainLemma.lean:428`),
`Newform.exists_nonzero_prime_eigenvalue` + `…lSeries_stripped…` (`CoeffSeq.lean`),
`petN_heckeT_p_symmetric_form` (`ConcreteFamily.lean`). The route-B chain avoids all of these.

---

## Confidence gate (Step 5) — status

1. Every leaf discharged from mathlib / project, or is an explicit API gap with a sub-tree:
   **YES** for L1, L2, L3, L4.0–L4.4, L_indep, L5, L6, L7. The **codisjointness** sub-problem
   (T012) is surfaced as an explicit API gap (NOT hand-waved). ✅ (with T012 flagged)
2. Lean skeleton compiles (`lake env lean`): **YES** — only `sorry` + 1 unused-var note. ✅
3. Every leaf has a verbatim source quote + Lean↔source paragraph: **YES** (above). ✅
4. Adversarial pass per leaf + internal node: **YES** — every node has an Attacks block
   (≥ 3 categories). The R-composition and L4 attacks surfaced T012 as the real risk. ✅
5. Prior-B2 log consulted: `.mathlib-quality/b2_log.jsonl` **absent** (no prior `/beastmode`
   B2 history for this project); created-as-empty check ⟹ no name/shape match. ✅
6. Tree mirrors source structure with cited internal nodes + grounded LOC: **YES** — internal
   nodes (R, L4, L4.3, L5, L6) all cite Miyake page/lemma; LOC anchored to Miyake source
   line counts (e.g. (i)+(ii) = 22 source lines ⟹ ~150 Lean). ✅

**Gate verdict:** PASSES for the buildable subtree (L1, L2, L3, L4.0–L4.4, L_indep, L5, L6,
L_indep). **T012 (decomposition codisjointness for `cuspFormsOldChar`) is the one
genuinely-open leaf**; tickets are created for it but it is flagged MED-LOW feasibility and
may require either the structural-equivalence theorem `cuspFormsOldChar = cuspFormsOld` (hard)
or accepting Mitigation B (an explicit `g ∈ cuspFormsOldChar ⊔ cuspFormsNew` hypothesis,
matching the master plan's framing and Miyake's `S_k(N,χ) = S_k^♭ ⊕ S_k^♯`).
