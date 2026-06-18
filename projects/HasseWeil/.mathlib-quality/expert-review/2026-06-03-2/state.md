# Expert-review session state (round 21)

- Generated: 2026-06-03
- Audience: the same senior arithmetic-geometry reviewer as rounds 1–20 (elliptic curves / isogenies / Weil pairing in char p)
- Goal of brief: specific-blocker guidance — is there a cheaper route to the one remaining geometric fact (the genuine comorphism's place-compatibility for 1−π, rπ−s), or is the ≈1000-line addition-formula coordinate development the honest cost?
- Scope: the single remaining Route 2A residual (order transport `hproj` / surjectivity `hsurj` / generic-point covariance `hgcomm` for the genuine isogenies 1−π and rπ−s over K̄)
- Depth: comprehensive (self-contained)
- Reply received: true (2026-06-03)
- Reply integrated: true (2026-06-03) — reply.md saved; verdict = CHEAPER ROUTE exists (formal-local), executing
- Verdict: do NOT do the ≈1000-line closed-point addition-formula specialisation. Instead: hgcomm (generic translation covariance) + formal linear coeff at O (= omegaPullbackCoeff, =1 for 1−π, =−s for rπ−s) + transport-by-translations ⇒ hproj. Plan: (1) hgcomm first; (2) hproj_of_hgcomm_and_unit_formal_linear_coeff (local action at P = action at O by translation, φ(P+R)−φ(P)=φ(R); unit linear term ⇒ e=1 ⇒ order transport); (3) hsurj from hproj via lying-over; (4) feed round-20 bridge. Q5: direct bilinear expansion gives scaling exponent for 1−π but NOT identification with deg — geometric compatibility still needed for general pencil.

## Questions in the brief (verbatim from §7)

| # | Question |
|---|----------|
| Q1 | (main) Is there a route to per-place order transport `hproj` for 1−π (and rπ−s) that REUSES the existing translation-transport machinery + a decomposition `1−π = "add P and −πP"` (via the order behaviour of −π, the addition morphism along the graph P↦(P,−πP), and translation-transport), rather than re-deriving an addition-formula coordinate specialisation from scratch? Or is the ≈1000-line development the irreducible honest cost? |
| Q2 | (surjectivity) Given we HAVE the genuine function-field comorphism φ^*:K(E)→K(E) and the finite extension [K(E):φ^*K(E)]=deg φ, is there a clean CoordHom-free proof of `hsurj` (III.4.10a) directly through the finite extension ("places extend"), WITHOUT first proving full place-by-place transport? Is the place↔point identification avoidable, or is it the same irreducible core (so hsurj+hproj should be proved together)? |
| Q3 | (generic-point covariance) Is `hgcomm` (φ^* commutes with translation at the generic point) provable cheaply directly from the explicit addition-formula comorphism + the group law on the generic point (no closed-point specialisation), or does it need the same machinery as hproj? |
| Q4 | (granularity) Should one build a SINGLE "geometric morphism" object for 1−π (comorphism + point map + place-compatibility, from the addition formula) and derive all of hproj/hsurj/hgcomm from it, or is per-facet proof cheaper? Is the addition-formula specialisation THE thing to build? |
| Q5 | (sanity/is the residual real) Is there any reformulation of the SEPARABLE SCALING itself that avoids per-place order transport for the pencil members — getting e_ℓ(φS,φT)=e_ℓ(S,T)^{deg φ} for φ=1−π using only π's Galois action + the already-proved [ℓ]-scaling + bilinearity, never transporting divisors through 1−π? |

## Ticket-board snapshot at brief time

No `/develop` tickets.md board in use for this phase; work tracked via the in-session task list.
Relevant completed milestones: weil pairing + props + nondeg (#36–#40), det-deg + matrix data + assembly (#41–#43, #48–#52), separable adjoint/scaling (#38, #46), CoordHom-free scaling + divisor-pushforward dual (#60, #61), base-change isogeny + finrank (#54, #56), separability of 1−π/rπ−s (#64, #65), GeometricRealization bridge (#67), ProjOrdTransport-for-1−π attack/verdict (#68).
OPEN deep residual: order transport `hproj` for 1−π, rπ−s (the addition-formula coordinate specialisation); plus `hsurj`, `hgcomm` for the same two isogenies.

## Stuck points (from §6 of brief)

1. `hproj` (order transport / divisor functoriality) for 1−π, rπ−s — the deepest; [ℓ] template (division-polynomial coordinate formula) does not transfer; needs the addition-formula specialisation (≈1000 lines).
2. `hsurj` (surjectivity III.4.10a) for 1−π, rπ−s — cannot be folded into hproj (principal divisors only); trace route circular; needs the place-compatibility or a new comorphism-side ramification-degree theory.
3. `hgcomm` (generic-point translation covariance III.8.2) for 1−π, rπ−s — bridge derives covariance + #ker=deg from it.

## Reference list (from §2.2 of brief)

[Silverman] Arithmetic of Elliptic Curves 2nd ed GTM 106 — II.2.6/2.7, II.2.12, III.4.10(a/b/c), III.5.1, III.5.2, III.6.1–6.2, III.8.1–8.6, V.1.1. Prior replies rounds 16–20 (this conversation).
