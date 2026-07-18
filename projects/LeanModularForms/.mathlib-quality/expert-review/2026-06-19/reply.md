# Reviewer reply — 2026-06-19 (Group A: Hecke eigenvalue arithmetic)

## Verdict
The proposed full-rank q-expansion lattice is **sufficient but substantially stronger than
necessary**. For k ≥ 2 the lightest standard route is a **finite integral modular-symbol /
cohomology module containing the Hecke eigensystems**, rather than an integral structure inside
S_k(Γ₁(N)) itself. Concretely: a finite-rank integral Hecke module H_ℤ + a Hecke-equivariant
**injection** S_k(Γ₁(N)) ↪ H_ℤ ⊗ ℂ. Take H_ℤ = torsion-free part of parabolic cohomology
H¹_par(Γ₁(N), Sym^{k-2}ℤ²), or an equivalent Manin-symbol module. Eichler–Shimura realizes the
complex cohomology as a Hecke module containing the cusp forms; Manin symbols give a finite integral
presentation. Hence: no integral model of X₁(N); no q-expansion principle; no rational/integral
basis of modular forms — **but some arithmetic realization of the Hecke action IS indispensable.**

## The minimal useful theorem (IHR — Integral Hecke Realization)
A finitely generated free abelian group H_{k,N} with integral actions of T_n (incl. bad-prime U_p)
and diamonds, plus an injective Hecke-equivariant ι : S_k(Γ₁(N)) → H_{k,N} ⊗ ℂ. Standard choice
H_{k,N} = H¹_par(Γ₁(N), Sym^{k-2}ℤ²)_tf. **Only injectivity of the period map is needed**;
surjectivity (full Eichler–Shimura) is unnecessary.

### Derivation of (A) and (B) from IHR
Let 𝕋_ℤ ⊆ End_ℤ(H_{k,N}) be the image of the integral Hecke algebra. Since H_{k,N} has finite
rank, End_ℤ(H) ≅ M_r(ℤ) is a finite ℤ-module, so 𝕋_ℤ (a subgroup) is finite free over ℤ. The
eigencharacter of a normalized newform f factors through 𝕋_ℤ as λ_f : 𝕋_ℤ → ℂ (by injectivity +
Hecke-equivariance). Put O_f = λ_f(𝕋_ℤ) ⊆ ℂ — finite over ℤ. Then a_n(f) = λ_f(T_n) ∈ O_f is
integral over ℤ ⟹ **(A)**. And ℚ ⊗ O_f is a finite-dim ℚ-algebra ⊆ ℂ, a domain hence a field,
containing K_f ⟹ **(B)**, with [K_f:ℚ] ≤ rank 𝕋_ℤ ≤ (rank H_{k,N})².

## Q1 — Is a q-expansion principle genuinely necessary?
**No, not in the proposed form.** A lattice inside the space of modular forms is unnecessary; an
integral Hecke module elsewhere containing the eigensystems suffices. BUT some arithmetic input of
this kind IS necessary: finite-dim complex linear algebra + formal Hecke relations do not force
arithmeticity. Counterexample: pick arbitrary (even transcendental) α_p and a character χ; define
λ_p = α_p, λ_{p^{r+2}} = α_p λ_{p^{r+1}} − χ(p)p^{k-1} λ_{p^r}, extend multiplicatively; on ℂe set
T_n e = λ_n e, ⟨d⟩e = χ(d)e. This satisfies all Hecke recursions/multiplicativity/diagonalization/
multiplicity-one with transcendental λ_p. So the abstract double-coset ring + recursion + finite-dim
do NOT force algebraicity. A direct proof that each T_n satisfies a monic ℤ-polynomial would prove
(A) but is essentially IHR again; and individual integral relations still wouldn't give (B)
(infinitely many algebraic integers can generate an infinite extension). Analytic bounds cannot
replace the arithmetic input.

## Q2 — Lightest route to full arithmetic structure
**Recommended: modular symbols / period cohomology** (Manin-symbol or vector-valued
period-polynomial module), not a scheme-theoretic modular curve. Build a finite integral module from:
the finite coset set Γ₁(N)\SL₂(ℤ); V_{k-2,ℤ} = Sym^{k-2}ℤ²; the Manin relations (order-2 / order-3
generators); the parabolic/boundary relation selecting cuspidal cohomology. Hecke acts via finite
sums of integral matrices. The required analytic theorem: the period map f ↦ ([α,β] ↦ (P ↦
∫_α^β f(z)P(z,1)dz)) is **injective and Hecke-equivariant** (the relevant half of Eichler–Shimura).
Much less than compactified generalized elliptic curves, Hodge bundle, integral models at p|N, Tate
curves, descent, cohomology-and-base-change.
**Geometric route (Deligne–Rapoport / Katz):** canonical but proves much more (integral schemes,
compactification, line bundles, base change, q-expansion principle). Preferable only if the project
will later need mod-p modular forms, Katz forms, congruences/reduction, Hasse invariants, integral
geometry at cusps, deformation / Galois-representation constructions. For just (A),(B): overpowered.
**Explicit spanning sets** (Eisenstein products, theta series, η-quotients): no standard uniform
theorem covering all N, all k ≥ 2, all χ, low-weight exceptions, lighter than modular symbols.

## Q3 — Is (B) cheaper than (A)?
**Yes, strictly.** Rational version (RHR): finite-dim ℚ-space H_ℚ + rational Hecke action + injective
Hecke-equivariant S_k(Γ₁(N)) ↪ H_ℚ ⊗ ℂ. Then 𝕋_ℚ ⊆ End_ℚ(H_ℚ) is a finite-dim ℚ-algebra, the
eigencharacter has finite-dim image, so K_f = ℚ(a_n) is a number field. This does **not** require a
rational form of the holomorphic space S_k itself — Betti cohomology supplies a rational space in
which S_k occurs after complexification; the holomorphic summand need not be ℚ-defined. The rational
theorem does NOT prove integrality (a ℚ-represented operator can have eigenvalue 1/2). For (A) you
need the integral lattice with correctly normalized integral Hecke action. In practice, once a
finite Manin-symbol module is built over ℚ, the same presentation over ℤ is a modest extra cost; the
hard analytic input (period injection) is common to both.

## Q4 — Can one work only with the chosen newform?
**No** way that avoids the same arithmetic issue. The complex Hecke span of an eigenform is just its
eigenline ℂf; no useful rank-1 ℤ-lattice (mult by a non-rational algebraic integer doesn't preserve
ℤf). The natural integral object has rank ≈ [K_f:ℚ] and contains all Galois-conjugate eigenlines —
but constructing it presupposes (1) K_f is a number field, (2) coefficientwise Galois conjugates are
again modular forms, (3) eigenvalues integral enough to define an order — i.e. the conclusions
sought. The Galois-orbit-span is circular until rationality is proven. Once the global integral
module exists, localize at f's eigensystem (useful downstream; doesn't reduce the input).

## Q5 — Cleanest atomic formal statement
**(FIH) Finite integral Hecke algebra.** Let 𝕋^full_{k,N,ℤ} ⊆ End_ℂ(S_k(Γ₁(N))) be the image of the
ℤ-algebra generated by ALL classical Hecke operators — including U_p for p|N and the diamonds. Then
𝕋^full_{k,N,ℤ} is a **finite ℤ-module**. This is exactly what (A),(B) consume; it avoids committing
the library interface to curves OR symbols. Behind it, cite the source theorem (IHR): a finite
integral modular-symbol/cohomology realization containing the cusp-form eigensystems. The proposed
full-rank q-expansion lattice is a STRONGER source theorem and is not the best atomic interface.

### Two corrections to the candidate q-expansion lattice
1. **Root-of-unity coefficients don't visibly preserve ℤ.** On a character space the coefficient
   formula contains χ(d): an algebraic integer but generally NOT in ℤ. Multiplication by χ(d)
   preserves O_{ℚ(χ)}, not ℤ. So {f : a_n(f) ∈ ℤ} is NOT visibly Hecke-stable per character — the
   natural per-character statement is an O_{ℚ(χ)}-lattice (eigenvalues then integral over ℤ since
   ℤ[ζ] is integral over ℤ). On the whole Γ₁(N)-space diamonds CAN act integrally on the correct
   global lattice, but proving that is itself part of the missing structure.
2. **A model over ℤ[1/N] is not enough for (A).** It gives integrality away from p|N but allows
   denominators at N. Need a genuinely integral Hecke action at bad primes (U_p) OR a separate
   local-newform argument for integrality of U_p-eigenvalues. The modular-symbol realization
   naturally includes integral bad-prime operators.

## Q6 — Weight/level caveats
- **k ≥ 2:** uniform via Sym^{k-2}ℤ² (k=2 → trivial coeff module ℤ). ✓ (our target).
- **k = 1:** (A),(B) still true but the cohomological construction does NOT extend (Sym^{-1}); use
  geometric q-expansion theory or weight-1-specific theory (Deligne–Serre). No gap for k ≥ 2.
- **Small N / torsion:** integral cohomology may have torsion (elliptic stabilizers, −I); quotient
  by torsion (H_ℤ ↝ H_ℤ/tors); Hecke preserves torsion, complexification kills it. When −I ∈ Γ₁(N)
  with incompatible weight parity, S_k = 0 (vacuous).
- **Nebentypus:** no difference globally on S_k(Γ₁(N)); per-χ use O_{ℚ(χ)} not ℤ.
- **Bad primes:** include U_p for p|N. Prime-power recursions determine a_{p^r} from a_p but do NOT
  manufacture a_p from good-prime eigenvalues; a T_n-only (good n) proof gives arithmeticity only for
  good coefficients unless a local-newform theorem is added.

## Recommended formal dependency
finite integral Manin-symbol module + integral full Hecke action + injective Hecke-equivariant
period map ⟹ 𝕋^full_{k,N,ℤ} finite over ℤ ⟹ O_f = λ_f(𝕋_ℤ) finite over ℤ ⟹ [ a_n(f) algebraic
integer for all n ; K_f/ℚ finite ]. **Do NOT formalize the integral model or full q-expansion
principle solely for (A),(B). Isolate the finite integral Hecke algebra theorem (FIH), or build it
through a finite Manin-symbol module + injective Eichler–Shimura period map** — the smallest
classical footprint proving both, uniformly for all k ≥ 2, N ≥ 1.

### References cited by reviewer
- Eichler–Shimura / group cohomology on arithmetic groups (arXiv:1701.00611).
- Manin, "Parabolic points and zeta functions of modular curves" (1972).
- Modular symbols for Γ₁(N) (Cambridge MPCPS).
- Deligne–Rapoport, "Les schémas de modules de courbes elliptiques" (geometric route).
- Deligne–Serre (weight 1).
