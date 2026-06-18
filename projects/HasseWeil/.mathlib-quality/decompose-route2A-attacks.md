# `/develop --decompose` adversarial pass — Route 2A (separable factorisation). 2026-05-31

Disposition: opposing the round-18-reviewer-endorsed Route 2A. Grounded in III.8 + III.5.5 (read this session).

## Route 2A (reviewer's recommended plan)
β=rπ−s = λ∘F^e (λ separable, F^e the relative p^e-Frobenius, deg F^e=p^e=deg_i β). det(β|E[ℓ])≡deg β via:
Frobenius compat e(F^eP,F^eQ)=e(P,Q)^{p^e} (Galois) + separable compat e(λA,λB)=e(A,B)^{deg λ} +
factorisation. Needs the Weil pairing on E AND the TWIST E^(p^e), the relative Frobenius, II.2.12.

## FINDING — a SIMPLIFICATION (Route 2A'): the twist/factorisation is AVOIDABLE; only the SEPARABLE case is needed

**Attack (is the inseparable factorisation/twist actually necessary?):** the attack SUCCEEDS — it isn't.

- **Silverman III.5.5 (read this session):** for β = m+nφ (φ = Frobenius), β is **separable ⟺ p∤m**. For
  β = rπ − s = (−s) + rπ: **separable ⟺ p∤s**. So:
  - **generic** (`genuineIsogSmulSub`, needs `s≠0` in K, i.e. p∤s): β **SEPARABLE**.
  - **edge `r≡0` in K** (p∣r, p∤s): β **SEPARABLE** (separability depends only on p∤s, not on r).
  - **edge `s≡0` in K** (p∣s): β inseparable — the ONLY inseparable case.
- So `det(β|E[ℓ])≡deg β` is needed via the pairing only for **separable β** (p∤s): the **separable
  compatibility** `e(βP,βQ)=e(P,Q)^{deg β}` on **E itself** (β an endomorphism) — **multiplicity-free,
  NO twist E^(p^e), NO relative Frobenius, NO factorisation.** This is the reviewer's I3 but for a
  separable *endomorphism*, the cleanest case (where the project's Pic⁰/comap dual sees full=separable
  degree).
- **The inseparable case (p∣s) is AVOIDED by the discriminant argument** (pure arithmetic, no EC):
  - From separable det≡deg + the shipped factor-by-factor `det((rπ−s)|E[ℓ])≡N`: `deg(rπ−s)=N` for **p∤s**.
  - `deg ≥ 0` ⟹ `Q(r,s):=qr²−trs+s² ≥ 0` for all `(r,s)` with **p∤s**.
  - **`Q ≥ 0` on `{p∤s}` ⟹ `t² ≤ 4q`**: if `t²>4q`, `Q` is indefinite; `{r/s : p∤s} = ℤ_(p)∩ℚ` is dense
    in ℝ, so some `(r,s)` with `p∤s` has `r/s` strictly between the two real roots of `Q(·,1)`, giving
    `Q(r,s) = s²·Q(r/s,1) < 0` — contradiction. (Formalises as: density of denominators coprime to p.)
  - `t² ≤ 4q` ⟹ `Q(r,s) ≥ 0` for **all** `(r,s)` (the form is positive semi-definite: `q>0`,
    discriminant `≤0`). Closes `qf_nonneg_skeleton` for ALL `(r,s)` — generic AND every edge —
    **uniformly**, obsoleting both `genuineIsogSmulSub_degree_eq_signed` and `degree_quadratic_exists_edge`.

**Why this is better:** trades the reviewer's twist infrastructure (pairing on E^(p^e), relative
Frobenius, II.2.12 factorisation, Frobenius pairing compat) for **one small arithmetic lemma** (p-coprime
denominators dense ⟹ pos-semidef from the p∤s sublattice). It also **never needs dual additivity nor the
abstract "deg is a QF"** (Silverman V.1.1's QF structure needs III.6.2c) — it uses only the *explicit*
value `deg(rπ−s)=N` for separable β and reasons about the *explicit* form `Q`.

## Route 2A' — refined plan (recommended)
1. **Weil pairing on E[ℓ]** (ℓ≠p), bilinear/alternating/nondegenerate (III.8 Prop 8.1) — on **E only**.
2. **Separable det≡deg:** `e(βP,βQ)=e(P,Q)^{deg β}` for **separable** β (mult-free separable adjoint /
   Pic⁰-comap), ⟹ `det(β|E[ℓ])≡deg β`. [the one remaining σ-bridge, MULT-FREE, separable case]
3. **Factor-by-factor `det((rπ−s)|E[ℓ])≡N`** (Galois for π + bilinearity + shipped `(rV−s)(rπ−s)=[N]`).
4. Combine (2)+(3) ⟹ `deg(rπ−s)=N` for **p∤s** (via the shipped `int_eq_of_congr_all_primes_ne`).
5. **Discriminant lemma:** `Q≥0 on {p∤s}` ⟹ `t²≤4q` ⟹ `qf_nonneg` for all `(r,s)`. Closes Leaf 1.

## Residual attacks on 2A'
- **Separable compat (step 2) is still a σ-bridge** — but MULT-FREE and separable, where the project's
  comap/Pic⁰ dual computes the full=separable degree (the regime that previously worked). Real but the
  tractable case. The genuine remaining core.
- **TORSION (E[ℓ]≅𝔽_ℓ²) + AG-SEP** dependencies from the first pass still stand (needed for the pairing).
- **Genuineness:** β=rπ−s must be a genuine isogeny for separable det≡deg — for p∤s, `genuineIsogSmulSub`
  exists (p∤s ⟹ s≠0 in K); ✓ matches its domain exactly.
- **Discriminant lemma (step 5):** needs density of p-coprime-denominator rationals — elementary,
  formalisable; verify the witness construction (s a power of a prime ≠ p, r=round(root·s)).

## Verdict
Route 2A' is sound and materially simpler than 2A (no twists/factorisation). The genuine remaining hard
core shrinks to the **separable** Weil-pairing det≡deg (step 2) — the mult-free case where the project's
existing Pic⁰/comap machinery applies — plus the pairing construction and the (elementary) discriminant
lemma. This is a real narrowing of the build surface.
