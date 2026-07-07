# Expert-review session state

- Generated: 2026-07-07 (second full brief; first was 2026-07-05, answered by v8)
- Audience: the v8 reviewer (senior arithmetic geometry; knows the project shape)
- Goal of brief: statement-drift audit + full-programme status check + post-v8 strategy/priority confirmation + mathlib-generality opinions
- Scope: whole project, all streams (A/B/C/D/E/F/Q/H/W + COH)
- Special feature: complete verbatim Lean signature appendix (drift-audit ground truth)
- Reply received: true (2026-07-07; verbatim archive at `reply.md`)
- Reply integrated: true (2026-07-07; owner "apply all" → `tickets.md` **Amendments v9**:
  work-order reset, W-stack/Q-finite split, T-A4 re-frozen (G-torsor form, blocked-B2 cleared),
  T-C0 sharpened, T-H7 parked, new tickets T-A8b/T-D33/T-B5z/T-GG-gen1/T-GG-gen2,
  [PROVED-MODULO-BOXES] convention)

## Reply outcome — headline drift RESOLVED (code was correct)

The reviewer's #1 concern (Γ₁(N) rank mismatch) was investigated against the Lean:
`IsGammaOne`/`Section.HasExactOrder` = `(orderDivisor P N).IsSubgroup E` where `orderDivisor`
is the **degree-N** divisor `[P]+…+[NP]` — a subgroup divisor, NOT equated to E[N]. `IsFullLevel`
= the **degree-N²** divisor `Σ_{(a,b)}[aP+bQ]` with `.ideal = torsionIdeal N` (= E[N]). Both match
KM/Deligne exactly; the drift was **prose-only** in the brief. Brief §2.1 and §4 corrected in place
(both output copies); NO Lean change needed, nothing downstream corrupted. Reviewer's "fix the code"
branch does not apply.

## Questions in the brief

| # | Question (abbreviated) |
|---|---|
| Q1 | Three-part drift audit: (a) LocallyWeierstrass def exactly as intended in v8? (b) full-set-of-sections/Drinfeld defs match KM Ch. 1/3? (c) GaloisRepData the right rendering of Buzzard p. 33? |
| Q2 | T-A4 re-freeze: endorse coordinate-uniqueness form of KM 2.2.5 (for fixed (E,ω), adapted coordinates unique up to x↦x+a, y↦y+ax+b)? How should ω enter formally? |
| Q3 | Strategy re-check: post-v8 execution (W bottom-up, T-W7 group law, D unchanged, F via in-project Galois correspondence) still the right sequencing? Anything to stop? |
| Q4 | Priorities: critical path reading (W3/4/5 → W7 → E-stream KM 4.7 + rigidity → W8) right? Marginal lane where? Early BB-DELIGNE worth it? |
| Q5 | Mathlib generality: parameterise fiber functor over IsSepClosure k Ω instead of THE SeparableClosure? Connected-étale-is-field decomposition right for mathlib? |
| Q6 | Weil pairing route: (b) char-0 étale-descent first then (a) KM 2.8 — concur? Reference for (b) at scheme level? |
| Q7 | Confirm coarse-moduli (j-line) deferral to post-fine-curves. |

## Stuck points (from §9 of brief)

1. T-A4 statement FALSE (2-isogenous counterexample); blocked-B2 awaiting re-freeze — Q2.
2. BB-DIFF gated on genuine mathlib gap (no relative-differentials sheaf API).
3. C-stream pairing-of-record unchosen (Q6).
4. BB-DELIGNE undischarged (blocks unconditional exact-order theory).
5. deleted-as-false: cocycle-free fppf descent of levelled curves (torsor form stands).

## Ticket-board snapshot pointer

Full board at brief time = projects/ModularCurves/.mathlib-quality/tickets.md as of commit (git log -1 --format=%H at save time; see integration doc when reply lands). Stream scoreboard copied in §7 of the brief.

## Reference list

[KM] Katz–Mazur 1985 · [Buz] Buzzard rough notes · [Loe] Loeffler notes · [GME] Hida 2012 · [Sil] Silverman 2009 · [DR] Deligne–Rapoport 1973 · [SGA1] Grothendieck LNM 224 · [Len] Lenstra Galois theory for schemes · [Con] Conrad 2007
