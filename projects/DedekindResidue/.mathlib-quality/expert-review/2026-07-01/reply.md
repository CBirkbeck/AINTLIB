# Reviewer reply — 2026-07-01

External number theorist. Verdict: **conditional green light.** Verbatim below.

---

I would give the plan a **conditional green light**. The logical decomposition is basically
right, and the choice to build the general Dedekind functional equation rather than rely on
abelian factorisation is mathematically sound. The main adjustment I would make is to treat
Tier 1 as slightly larger than "FE + Hadamard product": for the explicit formula and Stark
identity you will also need **finite-order/growth control, zero-counting or summability
infrastructure, and carefully normalised logarithmic-derivative statements**. Those should be
made explicit deliverables, not discovered later.

## Q1 — Overall decomposition

Yes: the four-tier structure matches the logical shape of BF15. The paper's theorem is an
explicit GRH-conditional approximation to the residue of the Dedekind zeta function, and the
brief correctly separates the field-specific analytic substrate from the paper-specific
estimates. The target theorem and approximant are stated in the brief exactly as a residue
approximation using the finite prime-ideal-power sum (f_K(X)). BF15 itself states GRH in the
zero-free half-plane form for both ζ_K and ζ_Q, then bounds |log κ_K − f_K(X)|.

The dependency order should be: Dedekind FE + analytic control ⇒ explicit formula / zero sums
⇒ BF15 Lemmas 2–5 ⇒ Theorem 1, Theorem 7, Corollary 8.

Your Tier 3 placement is correct: GRH really enters at the BF15 explicit-formula application
and continuation step, not in the construction of ζ_K. Lemma 3 is first proved for Re s > 1,
then continued to Re s > ½ using GRH to avoid zeros in the denominator and to make the
logarithm analytic.

The one dependency I would promote is **growth/order theory**. Your Tier 1 mentions the
Hadamard product and zero set, but the gap inventory should explicitly include: finite order
of Λ_K, enough vertical-strip bounds for contour shifts, local finiteness of zeros with
multiplicity, convergence conventions for zero sums, and a usable logarithmic derivative of
the canonical product. Without those, Tier 2 and Stark's formula will keep asking for lemmas
that were not budgeted.

## Q2 — Substrate route

My clear verdict: **use the classical Hecke theta route, not Tate's adelic route**, for this
formalisation.

Tate's thesis is conceptually cleaner on paper, especially for normalisations and local
factors, but in Lean it would require a very large adelic substrate: adeles, ideles, local
fields, self-dual Haar measures, Bruhat–Schwartz spaces, local Fourier transforms, local zeta
integrals, product formula bookkeeping, and measure normalisation. Unless that infrastructure
already exists, it is a much larger project than the theorem you are trying to prove.

The Hecke route is less elegant but much better aligned with what your brief says is already
available: Minkowski embeddings, lattice covolumes, fundamental domains for the unit action,
Mellin/Fourier transforms, Poisson-style infrastructure, and multivariable Fourier series.
Your proposed stack (P) Poisson → (Θ) Gaussian theta → (H) Hecke construction → (FE) is
therefore the right route.

I would, however, implement it in a **Hecke-classical proof with Tate-style normalisation
discipline**. That means: keep the proof in Minkowski/lattice language, but write every
measure, covolume, Fourier transform, discriminant factor, and archimedean gamma factor as if
you were preparing it for comparison with Tate. This is the best way to avoid the common
formalisation disaster where the functional equation is correct up to a hidden factor of
2^{r_2}, π^{r_2}, or √Δ_K.

I would also avoid making full Schwartz-class Poisson summation a blocker unless mathlib
already makes that natural. For the Dedekind FE, you mainly need Poisson for lattice
Gaussians, or at most for a small class of functions stable under linear change of variables.
A beautiful theorem for all Schwartz functions is reusable, but it may be a detour. The
efficient path is: (1) prove dual lattice and covolume identities; (2) prove Poisson for Z^n
in the class needed for Gaussians; (3) transport to arbitrary full lattices; (4) derive the
Gaussian theta transformation; (5) only then generalise Poisson if desired.

The deepest part is correctly identified as (H), not (P). The unit fundamental domain should
be isolated behind a small API: a theorem that converts the nonzero-element sum modulo units
into the partial zeta/Mellin expression. Everything downstream should see only that theorem,
not the geometry of the domain.

## Q3 — Abelian stepping stone

I would **not** use the abelian case as the main stepping stone toward the general theorem. It
closes the wrong gaps. The abelian route would exercise existing Dirichlet L-function
machinery, but it only gives the functional equation for abelian K, and even there requires
conductor–discriminant and product-of-root-numbers facts that are not presently part of the
intended general proof. Those are genuine number-theoretic formalisation projects, not
harmless warmups.

A useful compromise is to use abelian or K=Q cases only as **test harnesses** for the upper
tiers: the explicit formula API, the BF15 auxiliary function F_{s,X}, the Fourier transform
calculation, the T versus T−a trick, and numerical constant chasing. But I would not spend
months proving the abelian Dedekind FE through Dirichlet characters unless you need an early
publishable milestone independent of the general theorem. So: **skip abelian as a substrate
strategy; use it only as a validation target.**

## Q4 — GRH formulation and gap inventory

Your GRH formulation is mathematically acceptable, but I would change the Lean-facing
formulation. The paper's formulation is essentially zero-free: ζ_K(s) ≠ 0 and ζ_Q(s) ≠ 0 for
Re s > ½. The brief instead proposes "every zero of Λ_K lies on the critical line." That is
clean conceptually, but it may be less convenient mechanically.

For formalisation I would define two equivalent predicates after the FE is available:
GRH_Λ(K): ∀ρ, Λ_K(ρ)=0 ⇒ Re ρ = ½, and GRH_{>1/2}(K): ∀s, Re s > ½ ⇒ ζ_K(s) ≠ 0. Then prove
equivalence using the functional equation, Euler-product nonvanishing in Re s > 1, and the
fact that the gamma factors have no zeros and only cancel trivial zeros. For BF15 Lemma 3, the
zero-free half-plane form is probably the easiest hypothesis because it directly gives
analyticity of log(ζ_K/ζ_k) on Re s > ½. For the explicit formula, the critical-line
zero-indexed form is more natural because the zero sum is written over ρ = ½ + iγ_ρ, with
multiple zeros repeated.

Your gap inventory is close but should be expanded. In addition to dual lattices, Poisson,
Gaussian theta, Hecke construction, explicit formula, and Stark's formula, I would add:
- **Zero infrastructure.** Zeros as a locally finite multiset or indexed type with
  multiplicity, plus lemmas permitting sums over zeros to be compared, bounded, and
  subtracted. BF15 explicitly repeats multiple zeros in the zero sum.
- **Finite order and Hadamard product.** Stark's formula from the logarithmic derivative of
  the completed zeta requires more than meromorphic continuation and FE. It needs a
  canonical-product theorem instantiated for Λ_K, or a direct substitute strong enough to
  derive the logarithmic derivative identity.
- **Contour-shift estimates.** The explicit formula requires enough decay/growth to move
  contours and justify limiting horizontal integrals.
- **Branch of logarithm.** BF15 notes that the branch of log(ζ_K/ζ_k)(s) is real for real
  s > 1. That convention matters when continuing Lemma 3 and later taking s → 1.
- **Admissibility API for test functions.** BF15's explicit formula assumes evenness, bounded
  variation and integrability of F(x)e^{(1/2+ε)x}, bounded variation of (F(0)−F(x))/x, and the
  average-value convention at jumps. This should be a named structure, not assumptions copied
  into every theorem.

## Q5 — Hidden pitfalls

The most serious hidden pitfalls are normalisation, convergence, and endpoint conventions.
- **Archimedean constants.** Your convention Γ_C(s) = 2(2π)^{−s}Γ(s), not (2π)^{−s}Γ(s), is
  fine, but it changes the residue constant of Λ_K by a factor 2^{r_2} versus the other
  convention. Since BF15's explicit formula contains constants like −nC − n log(8π) − r_1 π/2,
  pin down one convention and write early conversion lemmas. This is exactly the kind of
  mismatch that can invalidate months of downstream constant chasing.
- **Conditional zero sums.** BF15 explicitly warns that the zero sum in the explicit formula
  has a convergence convention, and later uses absolute convergence only for the post-Lemma-3
  estimates. In Lean, this distinction should be visible. Do not represent all zero sums as
  absolutely summable series unless the theorem actually proves absolute summability for that
  transformed summand.
- **F_{s,X} admissibility checks are more annoying than they look.** The function is continuous
  at |t|=T, but its derivative has piecewise behaviour, and the bounded-variation hypotheses
  involve both exponential weighting and (F(0)−F(x))/x. Formalise a general lemma for functions
  that are piecewise C^1 with integrable derivative, rather than prove bounded variation from
  scratch each time.
- **Lemma 2 is independent of the substrate but not trivial in Lean.** The even extension,
  improper integrals, complex parameter h = s − ½, and denominator h²+γ² all need careful
  typing. Still, it is the best early concrete target above the definitions.
- **The T and T−a trick is a proof-engineering hotspot.** BF15 uses the mean value theorem and
  monotonicity estimates to avoid a lost log X factor; the difficult part will be proving the
  named real functions are monotone on the exact numerical domains needed for X ≥ 69, a = log 9,
  T = log X. The concern about constants (2.324, 3.88, 4.26) is justified.

## Bottom-line recommendation

Proceed with the general **Hecke theta stack**, not Tate and not the abelian shortcut. Make the
next milestone narrower than "prove the Dedekind FE": build a reusable lattice/Poisson/theta
layer, then a sealed Hecke partial-zeta theorem, then the completed Λ_K theorem with all
constants fixed. Add the missing Tier-1 analytic-control deliverables before implementation
begins.

Reference: arXiv:1305.0035, "Computing the residue of the Dedekind zeta function."
