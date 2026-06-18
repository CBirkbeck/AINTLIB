# Expert-review session state (round 24)

- Generated: 2026-06-10
- Audience: the same senior arithmetic-geometry reviewer as rounds 1–23
- Goal of brief: specific-blocker guidance — break the LAST wall of the dual-isogeny arc:
  #ker φ = deg φ for a general separable isogeny (Silverman III.4.10c). Candidate route W
  (one-good-fibre via Σef=deg + f=1 + almost-everywhere-unramified + place↔point dictionary)
  needs auditing; the new content is "separable ⟹ a.e. unramified" (different ideal vs
  discriminant vs derivative criterion).
- Scope: the Wall (§3) + secondary gaps G1 (II.2.12 existence / ker d = K^p), G2 (the
  Frobenius twist), G3 (witness-parametric architecture sanity).
- Depth: focused
- Reply received: true (2026-06-10)
- Reply integrated: true (2026-06-10)

## Questions in the brief (verbatim from §5)

| # | Question |
|---|----------|
| Q1 | (main) Route W the right formalization-grade proof of #ker=deg for separable φ? For step 2 (separable ⟹ all but finitely many places unramified): cheapest Dedekind formulation — (a) different ideal (in library), (b) discriminant of a primitive element, (c) derivative criterion? Pitfalls at the excised places? |
| Q2 | A route avoiding the generic-fibre count — direct surjectivity of ker φ → Aut(K(E₁)/φ*K(E₂)) (Galois descent without the count), or a duality/degree-pairing bootstrap from the constructed dual apparatus? |
| Q3 | G1: cleanest proof of ker(d) = K^p for a curve function field in char p (direct F(x)[y] computation vs 1-form theory); best route to Im(φ*) ⊆ K^p for inseparable φ? |
| Q4 | G2: is the Frobenius-twist construction routine (or name the subtlety); can dual-existence over 𝔽_q dodge the twist? |
| Q5 | (meta) Priorities: attack the Wall now vs III.6.2 layer (φ̂̂=φ, additivity) vs consolidate, given the LMFDB-catalogue goal? |

## Ticket-board snapshot at brief time

tickets-silverman.md Phase 6 (the dual arc DONE list: ramification formula + e≥1; hgcomm
general; fixed-field over any field; MulByIntBasepoint full n≠0; [ℓ]^ concrete; π̂=V;
faithful composition; arbitrary-dual reduction). Remaining walls list: [WALL-III.4.10c]
(THE wall), [II.2.12-EXIST], [TWIST], [ISO-BC], housekeeping. Commits 02ac7c9…55de460 +
board commit. A cleanup pass over the 11 dual-arc files is running concurrently.

## Stuck points (from §3/§4)

1. The Wall: #ker=deg general separable (III.4.10c) — reduces to ONE good fibre (T2 done);
   route W's new content = a.e. unramifiedness for separable extensions.
2. G1: II.2.12 existence (Im(φ*) ⊆ K^p for inseparable φ; ker d = K^p).
3. G2: the Frobenius twist E^(p) for deg_i not a q-power.
4. G3: witness-parametric dual architecture sanity before III.6.2.

## Reference list

[Silverman] Arithmetic of Elliptic Curves 2nd ed GTM 106 — II.2.6, II.2.11-12, II.4.2,
III.4.8-4.12, III.6.1-6.2. [Hartshorne] Algebraic Geometry GTM 52 — II.6.8-6.9.
Prior replies rounds 16–23.
