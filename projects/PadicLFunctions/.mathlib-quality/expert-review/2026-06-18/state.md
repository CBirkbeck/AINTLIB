# Expert-review session state

- Generated: 2026-06-18
- Audience: Iwasawa-theory specialist
- Goal of brief: can the ramified-CFT input (RJW step 2) be avoided / reduced to already-formalised infrastructure; both "avoid keeping 𝒳⁺" and "wholesale reformulation"; full IMC scope.
- Scope: full IMC (all primes), centred on the single ramified-CFT dependency of Stage G.
- Reply received: true (2026-06-18)
- Reply integrated: true (2026-06-18)

## Questions in the brief

| # | Question |
|---|----------|
| Q1 | Can Coleman/local reciprocity build 𝒰⁺/𝓔⁺ ≅ Gal(𝓜⁺_∞/𝓛⁺_∞) semi-locally, bypassing ramified global CFT? |
| Q2 | Can one work entirely on the minus class-group side (minus-MC + reflection ⟹ 𝒳⁺ MC), using only unramified CFT? |
| Q3 | Does the Euler-system (Thaine) route reach the MC without ever forming 𝓜⁺_∞? |
| Q4 | Is the ramified-CFT input intrinsic to the 𝒳⁺ statement or an exposition artifact; which ref minimises CFT surface? |
| Q5 | Does a Greenberg/Selmer (H¹) reformulation reduce the formalisation burden? |
| Q6 | Is axiomatising the sequence the right formalised/assumed boundary, or is there a smaller statement to assume? |

## Reviewer answers (one-line each)

- Q1: NO — the kernel = global-units closure is precisely the p-ramified part of global reciprocity (principal-idèle relation + existence theorem); Coleman/Chebotarev insufficient.
- Q2: YES (best genuine bypass) but precise — DIRECT-limit class group + Iwasawa–Kummer pairing (NSW 11.4.3 / Wa 13.32) + Iwasawa adjoint; reflected ODD components; **Vandiver does not make it short** (≈ full MC).
- Q3: YES for the class-group MC; NO for the 𝒳⁺ identification without a bridge (step 2 OR Kummer duality). Tower-level Euler system + reverse divisibility still to build.
- Q4: the exact sequence is NOT intrinsic; SOME global bridge is. Vandiver → Wa Cor 13.6 minimal; full non-ray-class → Euler system + Kummer (Wa 13.32 / NSW 11.4.3) + adjoint; minus-direct → Aoki.
- Q5: cleanest architecture, does NOT reduce current burden (needs continuous cohomology + local Tate duality + Poitou–Tate — major barriers; degree-one PT for μ_{p^m} ≈ the missing reciprocity).
- Q6: YES — but black-box the FINITE-LEVEL natural family Art_{n,p} (+ tower compatibility) and DERIVE the inverse-limit sequence via Mittag–Leffler. Follows RJW's actual source boundary.

## Ticket-board snapshot at brief time

Stage S (S1–S5) DONE; Stage G decomposed (G-DEF, G1, G2, G3, G4, G-VANDIVER, G-IMC + cleanups), blocked on G2 (ramified-CFT input). Plan in plan-G.md. Target = Vandiver-prime IMC reusing §12 iwasawa_theorem.

## Stuck points (from brief §6)

- The single obstruction: 0 → 𝓔⁺_{∞,1} → 𝒰⁺_{∞,1} → Gal(𝓜⁺_∞/𝓛⁺_∞) → 0 (Washington Cor 13.6), the (p)-ramified reciprocity bridge between the units/analytic side and 𝒳⁺_∞.

## Reference tags (from brief §2.2 + reviewer)

RJW23, Wa97 (Cor 13.6, Prop 13.22, Prop 13.32, Ch.15), CS06, MW84, Ru91/Lang, Gr89, NSW (Thm 11.4.3), Aoki (Gauss sums), Selecta (Fitting ideals of p-ramified Iwasawa modules).
