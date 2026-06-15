# Review brief (round 23) — Hasse bound via the finite-level Weil pairing (Route 2A): the last residual

*Prepared 2026-06-04 for the same senior arithmetic-geometry reviewer as rounds 1–22.
Self-contained but focused: a **single-residual** brief. Since round 22 the entire
unconditional Hasse bound has been **assembled and machine-checked to compile** — it now
carries `sorry` through exactly **one** remaining case of one of the three scaling leaves.
We ask how to close that last case: a cheap reduction-level workaround (route B) vs. a
larger geometric construction (route A), or a better idea.*

---

## 0. Orientation (one paragraph)

Goal: `|#E(𝔽_q) − q − 1| ≤ 2√q`, `E/𝔽_q`, `q = p^r`, via Route 2A. The bound is **assembled
end-to-end and compiles**: it reduces (axiom-clean) to three per-`ℓ` "scaling" identities
on `E[ℓ]` for the Frobenius pencil `{π, 1−π, rπ−s}` over `K̄`, for all primes `ℓ ≠ p`. Two of
the three leaves — the Frobenius `π` (via Galois equivariance) and `1−π` — are **closed,
unconditionally, axiom-clean**. The third leaf, the pencil `rπ−s`, is closed for all `(r,s)`
with **`p ∤ r` and `p ∤ s`** (and for `r = 0`); the **only** remaining gap is the case
**`p ∣ r`, `p ∤ s`**. This brief is about that one case.

## 1. Setup and what "the scaling leaves" are

- `π : E → E` is the `q`-power Frobenius; for an isogeny `φ`, `e_ℓ(φS, φT) = e_ℓ(S,T)^{deg φ}`
  is the Weil-pairing **scaling** (Silverman III.8.6). Reading this through the `ℓ`-adic
  representation `M = (π | E[ℓ])` gives `det(rM − sI) ≡ (\text{scaling exponent}) \pmod ℓ`.
- **Crucial design choice (round 22):** we do **not** prove the scaling exponent equals the
  geometric degree `deg(rπ−s)`. We use the exponent **`#ker(rπ−s)`** (a cardinality, hence
  `≥ 0`), which the pairing produces directly; the determinant computation gives
  `det(rM − sI) ≡ q r² − t r s + s² \pmod ℓ` independently (here `t = q + 1 − #E`). Varying
  `ℓ` forces the integer identity `q r² − t r s + s² = #ker(rπ−s) ≥ 0`, i.e. the Hasse
  quadratic form `Q(r,s) := q r² − t r s + s²` is `≥ 0`. This **eliminated** the need for
  `#ker = deg` (a separate hard fact) — a key simplification.
- So the chain is: **per-isogeny scaling** ⟹ `det(rM − sI) ≡ #ker(rπ−s)` ⟹ (vary `ℓ`)
  `Q(r,s) = #ker(rπ−s) ≥ 0` ⟹ (`Q ≥ 0` for enough `(r,s)`) ⟹ `t² ≤ 4q` ⟹ Hasse.

## 2. What is closed (axiom-clean: only `propext, Classical.choice, Quot.sound`)

- The whole pairing theory (bilinear/alternating/nondegenerate), the determinant reduction,
  and the integer-separation endgame.
- **Leaf π (Frobenius):** `e_ℓ(πS, πT) = e_ℓ(S,T)^q`, via Galois equivariance — the arithmetic
  Frobenius `σ` of `K̄(E)` (acting as the `q`-power on `K̄`, fixing the curve generators)
  satisfies `e_ℓ(σS, σT) = σ(e_ℓ(S,T))`, and `σ` acts as `ζ ↦ ζ^q` on `μ_ℓ`. The required
  geometric inputs (the divisor-Galois-descent `\mathrm{div}(σ g) = σ_*(\mathrm{div}\,g)` and the
  `σ`–translation covariance) are proved.
- **Leaf `1−π`:** `e_ℓ((1−π)S, (1−π)T) = e_ℓ(S,T)^{#E}`. Proved via a **surjectivity-free,
  dual-free** route discovered with your round-22 guidance: the scaling needs only the
  per-place order-transport (`ord_P(φ^* g) = ord_{φ(P)} g`) plus translation covariance,
  obtained from the addition-formula comorphism (`1−π = \mathrm{id} + (−π)`) by a
  closed-point/transport-to-`O` argument, with unramifiedness `e = 1` coming from the
  invariant differential (`φ^* ω = a_φ ω`, `a_φ ≠ 0`).
- **Leaf `rπ−s`, for `p ∤ r ∧ p ∤ s` (and `r = 0`):** same machinery as `1−π`, applied to the
  pair `(rπ, −s)`; the affine order-transport, the order at infinity (`−2`, `−3`), finiteness
  of `ker(rπ−s)`, and the covariance are all proved axiom-clean for these `(r,s)`.

## 3. The single remaining residual: the pencil scaling for `p ∣ r`, `p ∤ s`

For `(r,s)` with `p ∣ r` and `p ∤ s`, the isogeny `rπ − s` is **still separable** (its
invariant-differential coefficient is `−s ≢ 0`), so the *target* scaling
`e_ℓ((rπ−s)S, (rπ−s)T) = e_ℓ(S,T)^{#ker(rπ−s)}` is true and would close by the same
order-transport route as the `p ∤ r` case. The obstruction is purely in **constructing the
comorphism data** for this case in our framework:

- We build the pencil comorphism as the group-law addition of two summands, `rπ − s =
  (r·π) + (−s·\mathrm{id})`. The `−s` summand is `[−s]` (separable, `p ∤ s`). But the `r·π`
  summand is `[r] ∘ π`, and for `p ∣ r` the map `[r]` is **inseparable** (it factors through
  `[p] = `(Frobenius)∘(Verschiebung)). Our closed-point residue / order-at-infinity lemmas
  for a summand are currently proved through the explicit division-polynomial coordinates of
  `[r]`, whose key non-vanishing step is gated on `[r]` being separable (i.e. `p ∤ r`).
- Concretely, the one missing input is the order at infinity of the inseparable summand's
  pullback feeding the addition-formula pole count: `\mathrm{ord}_\infty\big((rπ−s)^* x\big) = −2`
  must be re-established when `[r]` is inseparable. We verified by hand that it **is** `−2`
  (the two summand poles are *asymmetric*: the `r·π` summand contributes `ord_∞ = q·M` with
  `M = \mathrm{ord}_\infty([r]^* x) ≤ −2`, the `−s` summand contributes `−2`, and the reduced
  addition numerator has a *unique* dominant term, giving `−2` exactly — this is **not** the
  symmetric three-way-tie degeneracy that blocks the general addition-pole lemma). So it is a
  genuine, tractable computation, but a sizeable one (≈ several hundred lines: the inseparable
  division-polynomial degree analysis + the addition construction + the bundle assembly).

## 4. The two routes we are weighing

**Route A — close the `p ∣ r` case geometrically.** Re-prove the inseparable
order-at-infinity `−2` (the asymmetric-pole computation above), build the addition-formula
comorphism for the inseparable `r·π` summand, and run the same order-transport assembly as
the `p ∤ r` case. Estimated ≈ 800 lines. Reliable (the mathematics is verified) but large,
and it is the *only* place the development must handle an inseparable summand.

**Route B — weaken the discriminant reduction so `p ∣ r` is never needed.** Currently the
step "`Q ≥ 0` everywhere" is deduced from "`Q(r,s) ≥ 0` for all `(r,s)` with `p ∤ s`" (all
`r`, including `p ∣ r`). The proof of `t² ≤ 4q` picks, for a large prime power `s = ℓ^n`
(`p ∤ s`), a *balanced* `r` with `|2qr − ts| ≤ q`, and derives a contradiction from
`Q(r,s) ≥ 0` if `t² > 4q`. If we instead only assume **`Q(r,s) ≥ 0` for `p ∤ r ∧ p ∤ s`**,
the conclusion `Q ≥ 0` everywhere still holds: an indefinite integral binary form has a
negative-value cone of positive measure, which contains a lattice point `(r,s)` with `p ∤ r`
and `p ∤ s` (the ratios `r/s` with `p ∤ r, p ∤ s` are dense). Then the pencil leaf is only
ever needed for `p ∤ r ∧ p ∤ s` — already done — and the `p ∣ r` case is **dropped entirely**.
Estimated ≈ 150–250 lines, but it is a number-theoretic existence argument (find a balanced
`(r,s)` with both coordinates prime to `p`) with more edge cases than the current single-prime
argument.

Both are mathematically sound. A is predictable but large and keeps an inseparable-summand
computation; B is much smaller and retires the last *geometric* residual outright, at the cost
of a fiddlier elementary number-theory lemma and a change to the reduction's hypothesis.

## 5. Questions

> **Q1 (the main one).** For the implication **"`Q(r,s) = q r² − t r s + s² ≥ 0` for all
> integer `(r,s)` with `p ∤ r` and `p ∤ s`" ⟹ "`Q ≥ 0` for all `(r,s)`"** (`q > 0`, `p`
> prime): is there a *clean, low-machinery* proof suitable for formalisation? The cleanest we
> see: if `t² > 4q`, exhibit one `(r,s)` with `p ∤ r, p ∤ s` and `Q(r,s) < 0`. Is there a
> slick explicit choice (e.g. a specific balanced `(r,s)` prime to `p`, or a CRT/pigeonhole
> construction) that avoids a general density argument? This is the crux of route B.

> **Q2.** Is route B's hypothesis change sound and **complete** for the Hasse conclusion —
> i.e. does `Q ≥ 0` on `{p ∤ r ∧ p ∤ s}` really suffice, or is there a subtlety (e.g. the
> `t = 0` case, or `q` divisible by `p`) where the dense-cone argument needs care?

> **Q3.** For route A: is `\mathrm{ord}_\infty` of an **inseparable** isogeny's coordinate
> pullback genuinely `−2` (unramified at `O`) — i.e. does "separable ⟹ `e_O = 1`" have a
> clean differential proof (`φ^* ω` nonvanishing at `O` ⟹ `e_O = 1`) that sidesteps the
> division-polynomial degree analysis for the inseparable summand? If so, route A shortens
> dramatically (the inseparable summand's pole follows from the *whole* map `rπ−s` being
> separable, not from the summand).

> **Q4.** Is there a **third route** we are missing — e.g. handling `p ∣ r` by an algebraic
> identity relating `rπ−s` (for `p ∣ r`) to the already-closed `p ∤ r` members, or a way to
> supply the `p ∣ r` scaling at the pairing level without the comorphism construction?

> **Q5 (meta).** Given the bound is fully assembled and only this one case carries `sorry`,
> which route would you take to a genuinely axiom-clean result, and is there any reason to
> prefer the geometric closure (A) over the reduction weakening (B) for the *integrity* of
> the formalisation (e.g. B's `#ker`-not-`deg` exponent leaving the bound not literally about
> `deg(rπ−s)`)?

## 6. Status summary

| Component | Status |
|---|---|
| Pairing, determinant reduction, integer separation | done, axiom-clean |
| `deg = #ker` simplification (avoids the geometric-degree identity) | done |
| Leaf π (Frobenius, Galois route) | **closed, axiom-clean** |
| Leaf `1−π` | **closed, axiom-clean** |
| Leaf `rπ−s`, `p ∤ r ∧ p ∤ s` (+ `r=0`) | **closed, axiom-clean** |
| **Leaf `rπ−s`, `p ∣ r ∧ p ∤ s`** | **the one open case — §3** |
| Full bound `hasse_bound_unconditional` | assembled + compiles; carries `sorry` only via the `p ∣ r` case |

## 7. Document metadata
- Project: Hasse bound for `E/𝔽_q` via the finite-level Weil pairing (Route 2A), Lean 4 / Mathlib.
- Brief: round 23, 2026-06-04. Continues rounds 1–22.
- Build status: compiles; `hasse_bound_unconditional` is assembled and carries `sorry` through
  exactly one case (`p ∣ r`, `p ∤ s`) of the pencil scaling leaf; everything else axiom-clean.
- Core ask: §5 — route B's elementary lemma (Q1/Q2), or a shortcut for route A (Q3), or a
  third route (Q4).
