# Expert-review session state (round 2)

- Generated: 2026-05-26 (round 2)
- Audience: same reviewer as round 1 (recommended Pic⁰)
- Goal: resolve the QF fork after discovering the shipped Pic⁰ dual is degree-blind
- Scope: the QF keystone `genuineIsogSmulSub_pivot_witness` (genuine dual pullback of rπ−s)
- Reply received: true (2026-05-26)
- Reply integrated: true (2026-05-26) — decision: B-narrow primary + C supporting; see integration.md

## Questions in the brief (round 2)

| # | Question |
|---|----------|
| Q1 | Given the shipped Pic⁰ dual is degree-blind (placeholder pullback), still favor completing the Pic⁰ comorphism (B), or move to K̄-extensionality (C)? |
| Q2 | Is there a degree route avoiding the genuine dual pullback — sep-deg·insep-deg (D), Weil pairing, height pairing — lighter than building the dual? |
| Q3 | For (C): is "isogeny determined by geometric point-map ⟹ degree" the right anchor, and does restricting to genuine isogenies collapse it back into (B)? |
| Q4 | Is the genuine dual pullback of rπ−s genuinely the irreducible §5.4 content — no degree-QF without it? |

## Finding driving round 2

Isogeny = (pullback, point-map) as independent data; `deg = finrank(pullback)`. `rπ−s`
inseparable ⟹ point-map fixes only sep-deg. Shipped `dualOfPicZeroPullback` uses a
PLACEHOLDER pullback (`:= α.pullback`) ⟹ degree-blind. So the keystone needs the GENUINE dual
comorphism; neither parked Wall A (V-side pole 3-way tie) nor shipped Pic⁰ provides it. The
critical-path `genuineIsogSmulSub_degree_eq_signed` (GapSpines) is open despite T9+trace+V-side
+Pic⁰ all in scope ⟹ irreducible against the codebase.

## Confirmed this session

- `verschiebung_dual_exists` (V=π̂) axiom-clean. `picZeroIsoE` (Pic⁰≅E) shipped. π+V=[t]
  point-map level + (rV−s)∘(rπ−s)=[N] hom level shipped.
- V.1.3: `bridge_Bi_isPrime_v2`, `bridge_Bi_liesOver_v2` shipped axiom-clean (committed).

## Round 1 reference
`.mathlib-quality/expert-review/2026-05-26/` (brief, reply, state, integration).
