# Expert-review session state (round 22)

- Generated: 2026-06-03
- Audience: the same senior arithmetic-geometry reviewer as rounds 1–21 (elliptic curves / isogenies / Weil pairing in char p)
- Goal of brief: SINGLE BLOCKER — the cleanest route to surjectivity of a nonconstant isogeny (1−π, rπ−s) on K̄-points (Silverman III.4.10a), given the geometric-point↔function-field-place seam in our two-field isogeny representation
- Scope: hsurj only (the last open input for the separable scaling; everything else built)
- Depth: focused (reviewer knows rounds 16–21)
- Reply received: true (2026-06-03)
- Reply integrated: in-progress (2026-06-03) — VERDICT: use R1 (lying-over + point↔place + hproj). Building `surjective_of_finite_comorphism_and_hproj` (Lemma A+B+C) at valuation-ring level.

## Questions in the brief (verbatim from §7)

| # | Question |
|---|----------|
| Q1 | (main) Cleanest route to surjectivity of a nonconstant isogeny on K̄-points, given: (i) proven bijection {closed K̄-points of E}↔{height-one places of K(E)}; (ii) comorphism φ* as a finite field extension of known degree; (iii) per-place order-transport ord_P(φ*g)=ord_{φP}(g) (hproj). Is the lying-over + point↔place + hproj route (R1) right, and what is the precise sequence turning "a prime of K(E) lying over the place at Q" into "a point P with φP=Q"? Does hproj already give the identification (so only ring-theoretic lying-over for φ*K(E)⊆K(E) is missing), or is there an extra step? |
| Q2 | Can route (R4) "image closed ⟹ surjective" be made precise using ONLY function-field/valuation data (e.g. "the set of places of K(E) restricting to a given place of φ*K(E) is nonempty") — never the scheme-theoretic image? Is this the same as (R1)? |
| Q3 | (necessity) Our point-map-fibre dual δ needs deg(φ*D)=#ker·deg D (hence surjectivity). Is there a construction of δ with δ∘φ=[#ker] provably a group hom WITHOUT surjectivity? (The naive "additive from hproj" is unsound — σ(ker) defect at non-image points.) |
| Q4 | (fallback) If surjectivity needs new infrastructure (function-field lying-over bridge, or Zariski-closed-image), what is the LEAST reusable lemma that discharges it for all separable pencil members (1−π, rπ−s, separable factors)? |

## Ticket-board snapshot at brief time

No /develop tickets.md. In-session task list relevant items: #79/#80 (1−π affine doubling/2-tor residues — built standalone, currently drift-broken, being repaired), #81 (assemble unconditional comap identity). The whole 1−π geometric pipeline (OneSubAffineResidues, OneSubInftyResidues, OneSubComapConcrete, AdditionPullback/SamePlace, DifferentialOrd, OmegaBaseChange, OrdAtInftyBaseChange, ProjOrdTransportLocal, OneSubProjOrdTransport) is UNTRACKED + not yet wired into root HasseWeil.lean.

## Stuck points (from §6 of brief)

1. (R1) lying-over for comorphism extension + point↔place + hproj — friction = connecting abstract finite field extension's ring-theoretic lying-over to geometric places + the point map (the geometric-point↔ring-place seam; same as the V.1.3 inertia/residue step).
2. (R2) dual route φ∘φ̂=[deg] — divisor dual gives δ∘φ (wrong order); two-sided (1−V)(1−π)=[#E] needs char-p dual additivity (round-16 wall).
3. (R3) division-poly coords — no global formula for the Frobenius-twisted addition 1−π.
4. (R4) image-closed⟹surjective — needs scheme-theoretic/Zariski-closed image, not expressible in the point-map framework.

## Reference list (from §3 of brief)

[Silverman] Arithmetic of Elliptic Curves 2nd ed GTM 106 — II.2.6/2.7, III.4.10(a)(c), III.5.1–5.2, III.6.1–6.2, III.8, V.1.1. Prior replies rounds 16–21 (this conversation).
