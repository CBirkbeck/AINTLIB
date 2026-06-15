# Expert-review session state (round 4)

- Generated: 2026-05-27
- Audience: same arithmetic-geometry reviewer as rounds 1–3 (elliptic curves over finite fields,
  isogenies, function fields; aware of the genuine-vs-placeholder-pullback formalization constraint)
- Goal of brief: specific blocker — V.1.3 `deg(1−π) = #E(F_q)`, the L5 geometric Frobenius-fixed
  descent, and the route choice (base-change to K̄ vs intrinsic Galois/translation)
- Scope: V.1.3 only (rounds 1–3 = the QF `qf_nonneg` witness)
- Reply received: true (2026-05-27)
- Reply integrated: true (2026-05-27) — Route B confirmed; L5 via coordinate fixed-point lemma
  (a^q=a ⟺ a∈F_q), NOT Lang; Route C parked; Route A abandoned. 4-step plan in integration.md.

## Questions in the brief

| # | Question (verbatim from §6) |
|---|------------------------------|
| Q1 | Route choice: given the alg-closed separable fiber count is already proved, is base-change-to-K̄-then-descend the right route to `deg(1−π) = #E(F_q)`, or is the intrinsic Galois/translation route C (kernel = Galois group of `K(E)/(1−π)*K(E)`) cleaner to formalize? |
| Q2 | The descent (L5): cleanest formulation + reference for "the q-Frobenius fixed locus on E(K̄) = E(F_q)"; is there an argument for `deg(1−π) = #E(F_q)` that avoids the geometric kernel entirely, or is passing through E(K̄) unavoidable? If unavoidable, Lang-style vs direct fixed-point computation? |
| Q3 | Route C tool: is "separable isogeny with rational (constant) kernel G ⟹ `K(E)/φ*K(E)` Galois with Gal ≅ G acting by translation, so `deg φ = #G`" correct + complete? Cleanest citation (Silverman III.4.10(b)? Mumford?)? Hidden hypotheses? Direct, or needs a separate "kernel = full Galois group" step? |
| Q4 | Architecture sanity: must the integration split the alg-closed fiber count from the finite-field point count across an explicit descent (the current lemma is gated on mutually-exclusive [alg-closed]∧[finite points] and wired to a placeholder isogeny)? Right top-level shape = Route B chain or Route C chain? Any reason to revive ramification Route A? |

## Ticket-board snapshot at brief time

No formal `tickets.md` for V.1.3 (the project tracks this witness via the decomposition artifact
`.mathlib-quality/decomposition.md`, 2026-05-27). Open sub-goals as understood:
- **L3** (open, API-gap): concrete base-change `(1−π)_K̄ = 1−Frob_K̄` + degree-equality. Scaffolded
  by the parametric base-change constructor + Frobenius base-change (prime char; general-q unfinished).
- **L5** (open, bottleneck): geometric descent `#ker((1−Frob)_K̄) = #E(F_q)` (q-Frobenius fixed locus
  on E(K̄) = E(F_q)). Currently an assumed-never-derived hypothesis in the integration layer.
- L4 (done): alg-closed separable generic-fiber count = sepDegree (proved, axiom-clean).
- L1/L2/L6 (ready/glue): sepDegree=degree (separable), degree base-change invariance, #E(F_q) def.
- Route C (alternative, unbuilt): kernel = Galois group of `K(E)/(1−π)*K(E)` via translations.

## Stuck points (from §4–§5 of brief)

- L5: geometric Frobenius-fixed-points = E(F_q) over K̄ (the descent) — bottleneck.
- L3: concrete base-change of `1−π` to K̄ as `1−Frob_K̄` + degree-equality.
- Route A (ramification over F_q) dead-ends at the same geometric fact (place→point surjectivity
  over a non-closed field; IsAlgClosed-only in our library).
- Architecture hazard: integration lemma gated on mutually-exclusive [IsAlgClosed]∧[Fintype Point]
  + wired to placeholder `1−π` (degree 1); descent hidden in the never-derived L5 hypothesis.

## Reference list (from §3)

- [Silverman 2009] *Arithmetic of Elliptic Curves*, GTM 106: II.2.6, III.4.5/4.10, III.5.5, V.1.1.
- [Mumford] *Abelian Varieties* — separable isogeny with constant kernel ⟹ Galois with group = kernel.
- Lang's theorem — `1−Frob` surjective on a connected group over F_q with kernel `G(F_q)`.
