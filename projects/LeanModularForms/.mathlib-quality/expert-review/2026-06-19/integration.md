# Reply integration — 2026-06-20

Reply: ./reply.md   Brief: ./brief.md

## Verdict
q-expansion principle / integral model of X₁(N) are **NOT needed** for (A) Hecke eigenvalues
algebraic-integral and (B) K_f a number field. Lightest route (k ≥ 2): a **finite integral
modular-symbol / parabolic-cohomology Hecke module** + an **injective** Hecke-equivariant period
map `S_k(Γ₁N) ↪ H_ℤ ⊗ ℂ` ⟹ the **finite integral Hecke algebra (FIH)** ⟹ (A),(B). Only injectivity
of the period map (the "easy half" of Eichler–Shimura), not the full isomorphism, is required.

## Interpretation summary
- Q1: q-expansion principle not needed; but SOME arithmetic input is (transcendental Hecke-system
  counterexample — abstract ring + recursion + finite-dim do not force algebraicity).
- Q2: modular symbols (Manin) lightest; geometric (Deligne–Rapoport/Katz) overpowered; no uniform
  Eisenstein/θ/η spanning set.
- Q3: (B) strictly cheaper — a rational Hecke module (Betti cohomology) suffices, no rational form of
  S_k itself.
- Q4: restricting to f is circular (eigenline; conclusions presupposed).
- Q5: cleanest atomic interface = (FIH); the proposed full-rank q-expansion lattice is not the best
  interface.
- Q6: k≥2 uniform (Sym^{k-2}ℤ²); k=1 separate (Deligne–Serre); U_p essential for (A); torsion-quotient;
  per-χ uses O_{ℚ(χ)}.
- **Two corrections to our prior plan**: (i) `{f : a_n ∈ ℤ}` is NOT T_n-stable over ℤ on a character
  space (χ(d) root of unity) — the "integral q-expansions" object was wrong; (ii) a ℤ[1/N] model is
  insufficient for (A) (bad primes).

## Changes applied
- **Rewrote** `.mathlib-quality/plan-coefficient-field-arithmetic.md`: replaced the
  q-expansion-principle / full-rank-lattice-in-S_k strategy with the layered FIH ← IHR
  (modular-symbol) plan. Layer 0 = FIH interface; Layer 1 = (A),(B) from FIH (provable now);
  Layer 2 = IHR via the Eichler–Shimura period pairing, decomposed into IHR-a (Manin module),
  IHR-b (integral Hecke action), IHR-c (period pairing analytic), IHR-d (injectivity). Added the
  cheaper B-only rational branch and the k≥2/U_p/torsion/nebentypus caveats.

## Changes rejected / deferred
- None rejected. The decision whether to fully formalise IHR-c/IHR-d (the analytic period
  pairing + injectivity) vs. isolate (IHR)/(FIH) as a cited classical input is deferred to after
  Layer 1 + the algebraic IHR-a/b are in place.

## Open questions remaining
- None left unanswered by the reviewer. New design question surfaced (not for the reviewer): the
  exact mathlib interface for the period integrals / group cohomology to use (groupCohomology vs a
  bespoke Manin-symbol module).

## Decisions recorded
- Target stays k ≥ 2, all N ≥ 1 (k=1 explicitly out of scope, needs Deligne–Serre).
- Atomic library-facing input = (FIH), with (IHR) as its mathematical justification.
