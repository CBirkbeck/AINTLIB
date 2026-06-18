# Reviewer reply — round 3 (2026-05-26): QF pole bound via the LIGHT formal-group route

*Verbatim record. Same reviewer.*

## Verdict

For the specific pole bound needed to make `rV−s` genuine, prefer the **formal-group /
kernel-of-reduction route** over Pic⁰ comorphism — but the LIGHT version, a
**formal-neighbourhood argument at O**, not full Silverman VII.2:
`t(P)∈𝔪 ⟹ t(rV(P)), t(−s(P))∈𝔪 ⟹ t((rV−s)(P))∈𝔪`, and if the formal series is nonzero then
`x((rV−s)(P)) ∼ t((rV−s)(P))⁻²` has a pole. This proves `ord_O((rV−s)*x) < 0` WITHOUT the
fragile coordinate leading-term computation. **Use formal groups for the local pole/nonconstancy
bound; use Pic⁰ comorphism for the global duality/degree statement if still needed. Complementary,
not identical.**

## Q1 — formal-group vs Pic⁰ for the pole bound? Formal-group.

The statement is local at O. Working in the local parameter `t = −x/y`, the group law is
`F(T₁,T₂) = T₁ + T₂ + higher`; if `T₁,T₂ ∈ 𝔪` then `F(T₁,T₂) ∈ 𝔪`, so the sum stays in the
formal neighbourhood of O and its x-coordinate has a pole — bypassing the 3-way tie
(`X₁²X₂, X₁X₂², −2Y₁Y₂`; V has no Frobenius order-scaling to break it). Minimal theorem:
```
theorem addPullback_x_has_pole_of_formal_nonzero (α β : Isogeny E E)
    (hα : formalIsogenySeries α ∈ T * K[[T]]) (hβ : formalIsogenySeries β ∈ T * K[[T]])
    (h_nonzero : formalGroupLaw W (formalIsogenySeries α) (formalIsogenySeries β) ≠ 0) :
    ordAtInfty (addPullback_x α β) < 0
```
Specialise α = rV, β = [−s]. Needs: (1) rV fixes O ⟹ series has zero constant term; (2) [−s]
fixes O ⟹ same; (3) formal sum not identically zero (rV−s ≠ 0); (4) then x has a pole.
**CAVEAT: only the nonzero case.** If rV−s = 0 the series is zero and there's no pole — that
branch stays separate (like L8z).

## Q2 — Does Pic⁰ comorphism rely on formal-group reduction? No — genuinely different.

Formal-group route: local at O (completed local ring / formal parameter t); content = E₁ closed
under addition/negation/isogenies-fixing-O; proves local nonconstancy/pole. Pic⁰ route: global
(divisors, principal divisors, push/pullback, Abel–Jacobi E ≅ Pic⁰); proves genuine global
pullback + duality. They touch the same geometry but prove different things. Route (a) is a LOCAL
SUBSTITUTE for one missing coordinate-transcendence proof; it does NOT replace the global duality
theorem.

## Q3 — Is the E₁ infrastructure tractable? Build the SMALL formal-neighbourhood package, not VII.2.

Minimal local package (formal-group IV.1–IV.3 style, NOT reduction VII.2):
1. `𝔪 = {u : ord(u) > 0}`.
2. Formal group law preserves it: `u,v ∈ 𝔪 ⟹ F(u,v) ∈ 𝔪`.
3. Formal inverse preserves it.
4. Any isogeny fixing O has formal series with zero constant term: `f_α(T) ∈ T·K[[T]]`.
5. Nonzero formal parameter ⟹ pole of x: `ord(t_α) > 0 ⟹ ord(x_α) < 0`.
Closing a TARGETED subset of the existing `FormalIsogenySeries` sorries (constant-term/positive-order
closure + addition-formula↔formal-group-law compatibility for the first coordinate). Do NOT build
full mathlib `Reduction` (it's coefficient-level); define the local/formal E₁ directly via t-adic
order. Good Lean targets: `formalGroup_preserves_positive_order : 0<ord u → 0<ord v → 0<ord (F u v)`
and `addPullback_x_has_pole_of_formalSeries_positive_order`.

## Strategic recommendation — split QF into two layers

- **Layer 1 (local genuineness of rV−s):** formal-group route. Goal `rV−s ≠ 0 ⟹ ord_O((rV−s)*x) < 0`.
  Unblocks the addIsog injectivity/transcendence requirement.
- **Layer 2 (degree/duality):** Pic⁰ or the available duality infra. Once rV−s is genuine, use
  K̄-extensionality / restricted dual additivity to prove `(rπ−s)^ = rV−s`, then QF closes.
This avoids forcing Pic⁰ to solve a local pole problem AND avoids the brittle global coordinate
computation.

## Hidden dependency

The formal-group pole proof assumes `rV−s ≠ 0`. If the branch is phrased as `rπ−s ≠ 0`, you need
`rπ−s ≠ 0 ⟹ rV−s ≠ 0` (follows from V = π̂ + additivity on the Frobenius plane, ~the theorem being
proved; alternatively prove both zero cases together via the trace/composition identities). So the
formal-group route is cleanest when the branch hypothesis is directly about `rV−s ≠ 0`, or when
enough duality is already available to transfer nonzeroness.

## Bottom line

For this specific genuine-rV−s pole bound: formal-group local route (genuinely different, lighter
than Pic⁰ comorphism), implemented narrowly (positive-order formal series ⟹ sum stays in formal
neighbourhood ⟹ x has a pole). Keep Pic⁰ for the global duality/degree part.
