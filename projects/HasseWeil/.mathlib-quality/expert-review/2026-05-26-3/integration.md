# Reply integration — round 3 (2026-05-26): QF pole bound = LIGHT formal-group route

Reply: ./reply.md   Brief: ./brief.md   State: ./state.md

## Decision (committed)

The QF keystone splits into two layers:
- **Layer 1 — local genuineness of rV−s (formal-group LIGHT route):** prove
  `rV−s ≠ 0 ⟹ ord_O((rV−s)*x) < 0` via the formal-neighbourhood argument at O — the formal
  group law `F(T₁,T₂)=T₁+T₂+…` preserves the maximal ideal `𝔪 = {ord > 0}`, so the sum of two
  positive-order formal series stays positive-order, and a nonzero positive-order parameter
  forces `x ∼ t⁻²` to have a pole. This BYPASSES the 3-way coordinate tie and discharges
  `addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_pole` (and hence the genuine rV−s).
  Build the MINIMAL formal-neighbourhood package (5 lemmas, IV.1–IV.3 style), NOT full
  Silverman VII.2 reduction, and NOT mathlib `Reduction` (coefficient-level). Define E₁ via
  t-adic order directly.
- **Layer 2 — degree/duality:** Pic⁰ comorphism OR K̄-extensionality / restricted dual
  additivity to prove `(rπ−s)^ = rV−s`, then `qf_nonneg` closes. Genuinely separate from
  Layer 1 (Pic⁰ does NOT rely on formal-group reduction).

## Minimal Layer-1 package (the 5 lemmas)

1. `𝔪 = {u : ord(u) > 0}` (on the local expansion / formal parameter).
2. `formalGroup_preserves_positive_order : 0<ord u → 0<ord v → 0<ord (F u v)`.
3. formal inverse preserves positive order.
4. isogeny fixing O ⟹ formal series ∈ T·K[[T]] (zero constant term).
5. `addPullback_x_has_pole_of_formalSeries_positive_order : 0<ord(t_α) → ordAtInfty(x_α)<0`,
   assembling into `addPullback_x_has_pole_of_formal_nonzero (α β) (hα hβ : series ∈ T·K[[T]])
   (h_nonzero : formalGroupLaw W (series α)(series β) ≠ 0) : ordAtInfty (addPullback_x α β) < 0`,
   specialised α=rV, β=[−s].

## Caveats / dependencies

- **Nonzero branch only:** the pole proof needs `rV−s ≠ 0`; the `rV−s = 0` case stays separate
  (like L8z). Phrase the branch hypothesis directly about `rV−s ≠ 0` if possible.
- **Nonzeroness transfer:** if the branch is `rπ−s ≠ 0`, need `rπ−s ≠ 0 ⟹ rV−s ≠ 0` (from V=π̂
  + additivity, ~the theorem; or handle both zero cases together via trace/composition identities).
- The existing `FormalIsogenySeries.lean` scaffold has open sorries; close only the TARGETED
  subset (constant-term/positive-order closure + addition-formula↔formal-group-law compatibility
  for the first coordinate).

## Settled (Q1–Q3)

Q1: formal-group for the pole bound. Q2: Pic⁰ ≠ formal-group (complementary). Q3: build the small
formal-neighbourhood package, not VII.2 / not mathlib Reduction.

## Changes

- QF ticket board: Layer-1 (formal-group pole) + Layer-2 (duality) recorded; the 5-lemma package
  + caveats. Memory `hasse-qf-route-pic0` updated.
- Next target: `formalGroup_preserves_positive_order` (foundational, self-contained).
