# Expert-review session state

- Generated: 2026-05-26
- Audience: the external reviewer from the prior Silverman round-trips (recommended Pic⁰,
  rejected the Frobenius-plane short-circuit)
- Goal of brief: strategic guidance — which route to commit to for the III.6.3
  degree-quadratic-form keystone (dual additivity (rπ−s)^ = rV−s on ℤπ + ℤ), or a simpler path
- Scope: the QF keystone only (V.1.3 noted as in-hand context)
- Reply received: true (2026-05-26)
- Reply integrated: true (2026-05-26)

## Questions in the brief

| # | Question |
|---|----------|
| Q1 | Which route for (rπ−s)^=rV−s given V, point-level π+V=[t], φ̂∘φ=[deg] mod existence are shipped — Pic⁰ / degree-square / explicit? Has the Pic⁰ steer changed? |
| Q2 | Is there a simpler path to Q(r,s)≥0 avoiding full dual additivity (parallelogram law; deg=#ker point-count; Weil pairing/determinant)? |
| Q3 | Is the Route-2 sign worry correct (degree-square gives only deg=|Q|; sign needs the genuine dual identification, so Route 2 isn't lighter than Pic⁰)? |
| Q4 | Is "a genuine isogeny is determined by its point-map" the right structural lemma; would it collapse Wall B and the Route-2 lift? |
| Q5 | Where to absorb ordinary/supersingular cleanest; do Pic⁰/degree-square avoid a case split or does it resurface? |

## Reviewer answers (summary)

- Q1: **Route 1 Pic⁰**, restricted to ℤπ+ℤ. Recommendation unchanged. Shipped facts reduce
  work but don't remove the bottleneck.
- Q2: No substantially simpler path. Parallelogram law ≡ III.6.3; point-count only for
  separable members + needs family kernel control; Weil/determinant valid but heavier;
  Cayley–Hamilton gives only |Q|. Torsion-determinant is the only serious alternative,
  likely heavier.
- Q3: **Yes, confirmed.** Degree-square → deg=|Q| only; sign fixed only by genuine dual
  identification. No sign-closure from q>0 or continuity alone.
- Q4: **Yes, invest** (restricted to genuine isogenies). Collapses much of Wall B. Does NOT
  replace the dual identification. Develop in parallel. Gave Lean shape.
- Q5: Absorb in **Verschiebung existence / inseparable-degree infrastructure**, not the QF
  proof. Routes 1/2 avoid the proof-level split; Route 3 forces it (Wall A).
- Extra: Wall A's blanket `ord_∞((rV−s)*x) = −2` should be audited — general formula is
  `ord_O(α*x) = −2·e_α(O)`, so −2 only when α separable at O.

## Project state at brief time (QF side)

- Bound assembled; sorry-free downstream of two HasseWitnesses leaves.
- V.1.3 (sep-deg(1−π)=#E) — decomposed, dispatchable (geometric ramification bridge); NOT
  this brief's subject.
- III.6.3 qf_nonneg — the open strategic question; three candidate routes.
- Shipped: Verschiebung dual existence (V=π̂, Vπ=πV=[q]); point-map trace π+V=[t]; φ̂∘φ=[deg]
  mod dual existence; genuine rπ−s (general-(r,s) pole bound = tactical wall); separability
  of 1−π; finite-dimensionality; pure-algebra discriminant spine.

## Reference list

Silverman GTM 106 (III.4 isogenies; III.6.1–6.3 dual isogeny / degree QF; V.1.1–1.3 Hasse);
Sutherland 18.783 Lecture 7.
