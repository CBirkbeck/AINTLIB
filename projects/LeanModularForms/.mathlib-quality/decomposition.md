# Decomposition (source-verified) — Group A: Hecke-eigenvalue arithmetic

*`/develop --decompose`, 2026-06-20. Sources read directly (NOT from memory): Diamond–Shurman
(`/tmp/ds.txt`), Shimura 1971 (`/tmp/shimura.txt`), both extracted from `refs/LeanModularForms/`.
Goal: enumerate EVERY irreducible block for `coeffSeq_isIntegral` (A) and
`instFiniteDimensionalCoeffField` (B). (Prior SMO decomposition backed up to
`decomposition-PRE-groupA-backup-2026-06-20.md`.)*

## Headline result of the decompose pass

> **There is exactly ONE irreducible block: the integral/rational structure on `S_k(Γ₁N)` =
> Eichler–Shimura (Shimura Chapter 8 / the Hecke-stable full-rank ℤ-lattice (3.5.20)).** It yields
> BOTH (A) and (B). The other candidate block — the bad-prime "Atkin–Lehner–Li" full-eigenform
> property — turns out **NOT to be a block**: Diamond–Shurman Thm 5.8.2(a) proves it elementarily
> from the **Main Lemma we already proved this session**.

This **corrects two pieces of received wisdom**: (i) the codebase docstring (`Newforms/Basic.lean:116–120`)
claiming the bad-prime property is "a separate development not currently formalised" (the explicit
Atkin–Lehner-sign route) — DS's actual proof avoids the signs entirely; (ii) the cited "DS Theorem
5.8.6" — that locator is an *Exercise* (`ds.txt:15464`); the real statement is **Thm 5.8.2(a)**.

## Source structure (read, with locators)

### Front (1) — integral structure ⟹ (A) + (B). Shimura §3.5 + Ch 8.
- **Shimura Thm 3.48(3)** (`shimura.txt:6818`): *"The characteristic polynomial of [X]_k for every
  X ∈ 𝒪 has rational integral coefficients."* Proof (`:6885`): *"Define ρ₀ with respect to a basis
  of L over ℤ. If e = [X]_k … e sends the lattice L into itself, so that ρ₀(e) ∈ M₂ᵣ(ℤ). Therefore
  the characteristic polynomial … must have integral coefficients."* → eigenvalue integrality (A).
- **Shimura Thm 3.51(1)** (`shimura.txt:6929`): `[D₀ : ℚ] = r` (the rational Hecke algebra is
  finite-dimensional, dimension `r = dim_ℂ S_k`). → number field (B).
- **Shimura Thm 3.52** (`shimura.txt:6978`): *"S_k(Γ') has a basis consisting of cusp forms of which
  the Fourier coefficients at ∞ are rational integers."* (the rational/integral structure).
- **THE deferral — (3.5.20)** (`shimura.txt:6853`): *"There is a discrete ℤ-submodule L of S_k(Γ') of
  maximal rank which is stable under the [Γ'αΓ']_k for all α ∈ Δ."* Shimura (`:6848`): *"The proof of
  this fact … is based on the following statement which we shall prove in **§ 8.4**."*
- **Shimura Chapter 8** = *"The cohomology group associated with cusp forms"* (`shimura.txt:254`):
  §8.1 group cohomology; **§8.2 the Eichler–Shimura isomorphism** `S_k ≅ H¹(Γ, Symᵏ⁻²)`
  (`:16555` *"an isomorphism of S_k(Γ,V) to the cohomology"*, Thm 8.4 `:16742`); §8.3 the Hecke
  action on cohomology; §8.4 the complex torus. Line `:582`: *"demands only a very elementary
  knowledge of homology and cohomology."*
- Weight-2 special case **(7.2.7)** (`shimura.txt:12485`): *"The eigen-values of [Γ₂αΓ₂]₂ are
  algebraic integers"* — via the endomorphism of the Jacobian acting on integral homology.

**Conclusion front (1):** the lattice (3.5.20) — equivalently the integral structure of `S_k(Γ₁N)` —
is **proven by Shimura via the Eichler–Shimura cohomology isomorphism (Ch 8)**. This is exactly the
reviewer's modular-symbol / cohomological route; it is *the same object*, not a cheaper alternative.
Elementary (group cohomology, no schemes) but a substantial development absent from mathlib.
**This is the single irreducible block.**

### Front (2) — bad-prime full eigenform. DS Thm 5.8.2(a). REACHABLE (not a block).
- **DS Definition 5.8.1** (`ds.txt:15320`): an *eigenform* is `f` with `T_n f = c_n f` and
  `⟨n⟩f = d_n f` for **all** `n` (= our `IsFullEigenform`).
- **DS Theorem 5.8.2(a)** (`ds.txt:15370`): *"Let f ∈ S_k(Γ₁(N))^new be a nonzero eigenform for the
  Hecke operators T_n and ⟨n⟩ for all n with (n,N)=1. Then (a) f is a Hecke eigenform, i.e. an
  eigenform for T_n and ⟨n⟩ for ALL n ∈ ℤ⁺. … Each such newform … satisfies T_n f = a_n(f) f for all
  n ∈ ℤ⁺. That is, its Fourier coefficients are its T_n-eigenvalues."*
- **DS proof** (`ds.txt:15355–15369`), verbatim core: *"For any m ∈ ℤ⁺ let g_m = T_m f − a_m(f) f,
  an element of S_k^new and an eigenform for T_n, ⟨n⟩ for (n,N)=1. … a₁(g_m) = a_m(f) − a_m(f) = 0,
  … showing that g_m ∈ S_k^old by the argument of the preceding paragraph. So g_m ∈ S_k^new ∩
  S_k^old = {0}, i.e. T_m f = a_m(f) f."* The "preceding paragraph" (`:15338`): a good-eigenform `h`
  has `a_n(h) = c_n a₁(h)` for `(n,N)=1`, so `a₁(h)=0 ⟹ a_n(h)=0 (n,N)=1 ⟹ h old by the **Main
  Lemma**.*

**Ingredients (all present in the codebase / just proven):**
- `a₁(T_n f) = a_n(f)` / `a_n = eigenvalue·a₁`: `aₘ_eq_eigenvalue_mul_aₒₙₑ` (MainLemmaProof.lean:259). ✓
- the **Main Lemma**: `mainLemma` (MainLemmaProof.lean:1592) — **PROVEN this session, axiom-clean**. ✓
- oldforms vanish at coprime indices: `coeff_eq_zero_of_mem_cuspFormsOld` (MainLemmaProof.lean:79). ✓
- `cuspFormsNew ⊓ cuspFormsOld = ⊥`: present (`Basic.lean:207`, "intersection is trivial"). ✓
- `T_n` preserves `cuspFormsNew` **for coprime n**: `heckeT_n_preserves_cuspFormsNew` (LevelRaiseComm.lean:656). ✓
- `oldPart`/`newPart` API (`oldPart_eq_zero`, `newPart_eq_self`, `newPart_add_oldPart`): Basic.lean:365–394. ✓
- **Only residual (small, NOT a block)**: the **bad-prime** versions for the `m | N` case of DS 5.8.2 —
  `U_p` preserves `cuspFormsNew`, and coprime `T_n` commutes with `U_p`. Routine Hecke-theory lemmas
  (the codebase has the coprime analogues + the Atkin–Lehner adjoint machinery in AdjointTheoryPetersson.lean);
  classical, bounded, not the deep Eichler–Shimura block. *(For coprime m, `T_m f = a_m f` is already
  immediate from f being a good-eigenform, so DS 5.8.2's g_m argument is only invoked at bad m.)*

**Conclusion front (2): REACHABLE.** Not a deep block. `Newform.isFullEigenform` decomposes into the
above, all in hand modulo two small lemmas. Overturns the codebase docstring.

## Decomposition tree (for the two NewformOrbit sorries)

```
(A) coeffSeq_isIntegral  +  (B) instFiniteDimensionalCoeffField
  │
  ├─ Layer 1 (DISCHARGEABLE, mathlib): a_n ∈ O_f = im(λ_f) finite over ℤ ⟹ IsIntegral (IsIntegral.of_finite);
  │     ℚ⊗O_f finite-dim domain ⟹ field ⊇ K_f (Finite.isField_of_domain / Subalgebra.isField_of_algebraic).
  │     [T001 done: heckeAlgℤ. T003/T004/T005 = the derivations.]
  │
  ├─ front (2): Newform ⟹ IsFullEigenform  [REACHABLE — DS 5.8.2(a) + mainLemma; NOT a block]
  │     needed so bad-prime a_n ARE T_n-eigenvalues (hence in O_f).
  │
  └─ front (1): FIH = heckeAlgℤ finite over ℤ   ⟸   ★ THE ONE BLOCK ★
        ⟸ Shimura (3.5.20) integral lattice L ⟸ Shimura Ch 8 = Eichler–Shimura cohomology iso
          (= integral Manin-symbol / period realization; the reviewer's IHR). Absent from mathlib.
```

## Adversarial notes (composition attacks)

- *Could (A),(B) be true without front (1)?* Attack: eigenvalues of a finite-dim ℂ-operator are
  algebraic only if it is defined over ℚ̄; a ℚ-subalgebra of `End_ℂ` need not be finite-dim.
  **Survives:** both A and B genuinely need the rational/integral structure (front 1) — no shortcut.
  (Confirmed against Shimura: 3.48(2) `B = B₀⊗ℂ` and 3.51 both invoke L.)
- *Is front (2) circular with the Main Lemma?* Attack: does `g_m ∈ old` use anything needing
  full-eigenform? **Survives:** `g_m` is a *good*-eigenform (coprime n); the Main Lemma needs only
  coprime-coefficient vanishing, which `a₁(g_m)=0` + the recurrence give. No circularity.
- *Does the cited "DS 5.8.6" exist as a theorem?* Attack: **FAILED for the citation** — 5.8.6 is an
  Exercise (`ds.txt:15464`); the real theorem is 5.8.2(a). Citation corrected.
- *Is front (1) avoidable via the abstract Hecke ring?* Attack (reviewer Q1, re-checked vs Shimura
  3.48): the abstract double-coset ring + recursion do NOT force algebraicity (transcendental
  Hecke-system counterexample); integrality comes only from the lattice L. **Survives: front (1) is
  irreducible.**

## Feasibility assessment

The decomposition bottoms out at **exactly one** irreducible block — the integral structure on
`S_k(Γ₁N)`, which Shimura proves via the **Eichler–Shimura cohomology isomorphism (Ch 8)**, i.e. the
cohomological/modular-symbol route. Everything else is reachable now: T001 is done; the Layer-1
derivations (A,B from FIH) are mathlib one-to-three-liners; and front (2) (bad primes) is an
elementary consequence of the just-proven Main Lemma (DS 5.8.2(a)), **not** the separate
Atkin–Lehner–Li development the docstring feared. Net: **2 sorries → 1 deep classical input
(Eichler–Shimura)**, with both bad-prime coverage and the number-field property reachable from
in-hand results. The one block is a real multi-component formalisation (integral group cohomology
`H¹(Γ₁N, Symᵏ⁻²ℤ²)`, the period/Eichler–Shimura iso, the integral Hecke action) absent from mathlib —
elementary (no algebraic geometry), and the genuine, precisely-located irreducible core.
