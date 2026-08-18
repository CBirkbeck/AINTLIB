# Mathlibable assessment — `Chebotarev.summable_prime_absNorm_rpow`

**Verdict: NO-composable-from-mathlib**

Qualified name: `Chebotarev.summable_prime_absNorm_rpow`
Source: `projects/Chebotarev/CebotarevDensity/Density.lean:112`

---

## 1. The declaration

```lean
namespace Chebotarev
variable {K : Type*} [Field K] [NumberField K] {S : Set (Ideal (𝓞 K))} {δ : ℝ}

/-- Over the nonzero prime ideals of `𝓞 K` lying in any set `S`, the series `Σ_𝔭 N𝔭^{-s}` is
summable for `1 < s`. -/
theorem summable_prime_absNorm_rpow (S : Set (Ideal (𝓞 K))) {s : ℝ} (hs : 1 < s) :
    Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
      (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) := by
  have hi : Function.Injective
      (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
        (⟨𝔭.1, 𝔭.2.2.2⟩ : NonzeroIdeal K)) :=
    fun a b hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab)
  exact ((summable_nonzeroIdeal_absNorm_rpow hs).comp_injective hi).congr fun _ ↦ rfl
```

**What it says.** For a number field `K`, an arbitrary set `S` of ideals of `𝓞 K`, and a real
`s > 1`, the family `𝔭 ↦ N𝔭^{-s}` indexed by the *nonzero prime* ideals lying in `S` is summable.

**How it is proved.** It is a one-line restriction of the project's own
`summable_nonzeroIdeal_absNorm_rpow` (summability over **all** nonzero ideals) to the prime/`S`
subtype, via the injection into `NonzeroIdeal K` and `Summable.comp_injective`. The base fact
`summable_nonzeroIdeal_absNorm_rpow` is itself a real-`rpow` shadow of the project's
`hasSum_nonzeroIdeal_absNorm_cpow` (the complex-`cpow` Dedekind-zeta Dirichlet-series convergence,
`NumberFieldEulerProduct.lean:514`), obtained by `.summable.norm.congr`.

Dependency chain inside the project:
`hasSum_nonzeroIdeal_absNorm_cpow` (HasSum, ℂ, all nonzero ideals)
→ `summable_nonzeroIdeal_absNorm_rpow` (Summable, ℝ, all nonzero ideals, **private**)
→ **`summable_prime_absNorm_rpow`** (Summable, ℝ, nonzero primes in `S`).

This lemma is pure Dirichlet-density bookkeeping: it is consumed by `primeIdealZetaSum_le_univ`,
`primeIdealZetaSum_le_of_subset`, `primeIdealZetaSum_union_of_disjoint`, etc., to manipulate the
partial Dirichlet series `Σ_{𝔭∈S} N𝔭^{-s}`.

---

## 2. Literature search — the standard statement

| Source | Statement of convergence | Index set |
|---|---|---|
| Wikipedia, *Dedekind zeta function* | `ζ_K(s)=Σ_𝔞 N(𝔞)^{-s}=∏_𝔭 (1−N𝔭^{-s})^{-1}`; series and product **converge absolutely for σ=Re(s)>1**; abscissa of (absolute) convergence is σ=1 | all nonzero **ideals** 𝔞 (Euler product over all primes 𝔭) |
| PlanetMath / HandWiki, *Dedekind zeta function* | same; sum over all nonzero ideals, Euler product over all prime ideals; absolutely convergent on Re(s)>1 | all nonzero ideals / all primes |
| Moss (Harvard 223a), Baidoo (UChicago REU) — *Dirichlet series & Dedekind ζ* | `ζ_K(s)=Σ a(n)/n^s`, `a(n)=#{𝔞 : N𝔞=n}`, absolutely & uniformly convergent on compacta of Re(s)>1 | Dirichlet series in `n` = ideal-counting coefficients |
| Sharifi, *Algebraic Number Theory* §7.1 (the project's reference) | the denominator `Σ_𝔭 N𝔭^{-s}` is the Dirichlet density normaliser, `~ log(1/(s−1))` as `s↓1` | all nonzero primes |

**Takeaways.**
- The literature-standard convergence statement is over **all nonzero ideals** (or the Euler
  product over **all** primes). Convergence for `Re(s)>1` is the textbook *starting point* of
  Dedekind-zeta theory — universally stated, never restricted to "primes in an arbitrary set `S`".
- Restricting the convergent positive series to a sub-index (primes only, and only those in `S`) is
  trivial domination/monotonicity — it is never a separately-named theorem in the literature; it is
  the "obviously a sub-series of a convergent series of positive terms" remark.

So the canonical, citable object here is the **unrestricted** summability over all nonzero ideals
(equivalently the Euler product over all primes), *not* the prime-in-`S` restriction.

Sources:
- https://en.wikipedia.org/wiki/Dedekind_zeta_function
- https://planetmath.org/DedekindZetaFunction
- https://handwiki.org/wiki/Dedekind_zeta_function
- https://abel.math.harvard.edu/archive/223a_2008/s06.pdf
- https://math.uchicago.edu/~may/REU2016/REUPapers/Baidoo.pdf

---

## 3. Mathlib search — is it already there, or a more general form?

Methods used: on-disk grep of the pinned mathlib (`.lake/packages/mathlib`), `WebSearch` over
`leanprover-community.github.io/mathlib4_docs`. (`lean_loogle`/`lean_leansearch` not available in
this harness; the mathlib tree is on disk and was searched directly.)

**Dedekind zeta in mathlib** — `Mathlib/NumberTheory/NumberField/DedekindZeta.lean` (X. Roblot, 2025):
- `NumberField.dedekindZeta s := LSeries (fun n ↦ Nat.card {I : Ideal (𝓞 K) // absNorm I = n}) s`
  — defined as an **`LSeries`** in the ideal-counting coefficients.
- `NumberField.dedekindZeta_residue`, `dedekindZeta_residue_pos`,
  `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT` (the **Dirichlet class number formula**:
  residue at `s=1`).
- Supporting: `Mathlib/NumberTheory/NumberField/Ideal/Asymptotics.lean`
  (`Ideal.tendsto_norm_le_div_atTop₀`, ideal-counting asymptotics).

**Key gap.** Mathlib does **not** expose a directly-usable
`Summable (fun I : Ideal (𝓞 K) ↦ (Ideal.absNorm I : ℝ) ^ (-s))` (or `… : ℂ) ^ (-s)`) lemma. A grep
for `absNorm … Summable` / `dedekindZeta … Summable` / `LSeriesSummable … dedekind` across all of
`Mathlib/` returns nothing. The absolute convergence for `Re(s)>1` exists only *implicitly* inside
the `LSeries` / `LSeriesSummable` layer (one would have to feed the ideal-counting asymptotics into
`LSeriesSummable` results to extract it), never as the plain "the ideal-norm series is summable"
statement that the project needs. So even the **base** fact
(`summable_nonzeroIdeal_absNorm_rpow` / `hasSum_nonzeroIdeal_absNorm_cpow`) is not in mathlib as a
ready lemma — and *a fortiori* the prime-in-`S` restriction is not.

**The restriction lemma, however, IS in mathlib.**
`Mathlib/Topology/Algebra/InfiniteSum/Group.lean`:
```lean
theorem Summable.comp_injective {i : γ → β} (hf : Summable f) (hi : Injective i) :
    Summable (f ∘ i)                                    -- :293 (additive of Multipliable.comp_injective)
theorem Summable.subtype (hf : Summable f) (p : β → Prop) :
    Summable (f ∘ (↑) : Subtype p → α)                  -- :300 (= comp_injective Subtype.coe_injective)
```
This is exactly — and verbatim — the tool the proof uses to pass from "all nonzero ideals" to
"primes in `S`".

---

## 4. Generality analysis vs. the literature-standard form

This declaration is *strictly more specialised* than the canonical statement, in two independent
directions:

1. **Index restriction.** The literature/canonical object is "all nonzero ideals" (or "all
   primes"). This lemma restricts to **nonzero primes ∧ membership in an arbitrary set `S`**. That
   `S`-and-primality predicate is bespoke Dirichlet-density plumbing with no mathematical content of
   its own — it is the generic "a sub-family of a summable nonneg family is summable" instance.
2. **Scalar specialisation.** It is the **real-`rpow`** shadow of the already-proven
   **complex-`cpow` `HasSum`** (`hasSum_nonzeroIdeal_absNorm_cpow`). The complex `HasSum` over all
   nonzero ideals is the stronger, more reusable statement.

Hence this is **not** a candidate for "YES-but-generalise-first" by tweaking *this* statement: the
right generalisation is to drop the `S`/prime predicate **and** the real specialisation entirely,
which lands you back on the **base** lemma (all nonzero ideals; `HasSum`/`Summable`; ℂ and/or ℝ).
That base lemma — the project's `hasSum_nonzeroIdeal_absNorm_cpow` /
`summable_nonzeroIdeal_absNorm_rpow` — is the genuinely mathlib-worthy object in this neighbourhood
(it is exactly the missing "Dedekind-zeta Dirichlet series converges for Re s>1" lemma), and it
should be upstreamed alongside / under `NumberField.dedekindZeta`. **This** declaration is just the
thin convenience wrapper sitting on top of it.

---

## 5. Composition check — can ≤3 mathlib calls give it?

Yes — and this is decisive. Take as given the **base** summability over all nonzero ideals (call it
`H : Summable (fun I : NonzeroIdeal K ↦ (Ideal.absNorm I.1 : ℝ) ^ (-s))`). Then:

```lean
H.comp_injective hi            -- hi : the prime/S-subtype ↪ NonzeroIdeal K injection
  |>.congr (fun _ ↦ rfl)       -- defeq repackaging of the index
```

That is **one** essential mathlib lemma (`Summable.comp_injective`; the `congr` is a defeq cosmetic
step), plus the one-liner injectivity proof. Equivalently `H.subtype …` after transporting along the
obvious equiv. Either way it is `≤ 3` mathlib calls on top of the base fact.

The base fact `H` is precisely what is *not* in mathlib yet and would be the thing to add. Given `H`,
this prime-in-`S` lemma carries no additional mathematical weight — it is a mechanical restriction
that any user can write inline. That is the definition of NO-composable-from-mathlib.

---

## 6. Verdict

**NO-composable-from-mathlib.**

- The declaration is a one-`Summable.comp_injective` restriction of a more fundamental fact
  (summability of the ideal-norm Dirichlet series over **all** nonzero ideals) to "nonzero primes in
  an arbitrary set `S`". The restriction lemma (`Summable.comp_injective` / `Summable.subtype`) is
  already in mathlib; the prime/`S` predicate is project-specific Dirichlet-density bookkeeping with
  no standalone mathematical content. → not worth adding as-is.
- It is also strictly less general than the literature-standard statement (all nonzero ideals; the
  complex `HasSum`), so it is not a "generalise this statement" candidate either — generalising it
  collapses it onto the base lemma.

**Adjacent recommendation (out of scope for this single-decl verdict, recorded for the
coordinator).** The *base* fact — the project's `hasSum_nonzeroIdeal_absNorm_cpow` /
`summable_nonzeroIdeal_absNorm_rpow` (convergence of `Σ_𝔞 N𝔞^{-s}` for Re(s)>1, over all nonzero
ideals) — **is** mathlib-worthy: it is the textbook Dedekind-zeta convergence statement that mathlib
currently leaves implicit inside the `LSeries`/`LSeriesSummable` layer and does not expose as a
usable `Summable`/`HasSum` lemma next to `NumberField.dedekindZeta`. That is the right thing to
upstream; **this** declaration is its thin downstream wrapper and should stay in the project.
