# Reply integration — 2026-05-21

Reply received from: AI mathematical reviewer, 2026-05-21.
Brief: ./brief.md
Reply: ./reply.md

## Headline

Reviewer warned the milestone was likely mispackaged: the raw unweighted double-coset sum is NOT representative-independent on a nebentypus χ-space (stabilizer-character obstruction), and asked us to AUDIT whether the existing general-χ construction (`twistedHeckeRingHomFunction` / `twistedHeckeSlash_gen`) is genuinely χ-twisted or raw.

**Audit verdict: (A) TWISTED/CANONICAL.** `twistedHeckeSlash_gen` carries a genuine character weight `δ₀(αᵢ)⁻¹ • (f|_k αᵢ)`; representative-independence is genuinely PROVEN (`twisted_weighted_slash_tRep_gen_of_mem`, `twistedHeckeSlash_gen_preserves_invariant`); the reviewer's χ(d_γ) obstruction is cancelled by the δ₀(γ)⁻¹ weight using f's twisted-invariance. Assembled into an honest RingHom `twistedHeckeRingHomFunction` over 𝕋(Γ₀(N)). Reduces to trivial-χ `heckeSlash_gen` when χ=1.

Consequence: the "hard" χ-equivariance content (brief §8.1, budgeted 1-2 weeks) is ALREADY DONE inside the twisted construction. The reviewer's "repair step 1" (diamond-eigenspace ↔ Γ₀(N)-twisted-slash equivalence) ALSO already exists and is proven (`modFormCharSpace_iff_nebentypus`, `gamma0TwistedSlashModFixedSubmodule_eq_modFormCharSpace`), with d_γ = lower-right convention confirmed. Remaining gap is narrower and mechanical: wire the FUNCTION-level twisted ring hom to the ModularForm-level `modFormCharSpace k χ`.

## Interpretation summary

| # | Reviewer point | Type | Reconciliation after audit |
|---|----------------|------|----------------------------|
| 1 | Raw sum not rep-independent for χ≠1 | concern (correct in general) | Doesn't bite us — our action is χ-weighted & rep-independent |
| 2 | Audit Result 5.4 | direct ask | Done: TWISTED/CANONICAL |
| 3 | Don't introduce Γ₁(N) ring; keep Γ₀(N) pivot | direct answer | Confirmed (we use 𝕋(Γ₀(N))) |
| 4 | Φ_χ is χ-dependent repn of same algebra; make explicit | API guidance | Confirmed; target End(modFormCharSpace k χ) makes it explicit |
| 5 | Clean route: identify holomorphic V_χ with M_k(Γ₁(N),χ) and transport | recommended path | CHOSEN — step 1 already exists; only transport remains |
| 6 | Generator-based route (T(1,p),T(p,p),U_p bridges) | alt path | Deferred to stage 2 (bridge to concrete heckeT_n) |
| 7 | Convention risk: lower-right d vs upper-left a | caution | Real; δ₀-weight uses upper-left-of-raw = lower-right-of-adjugated. Add 1-line confirming lemma |
| 8 | Bad primes U_p: include deliberately | direct answer | Handle in stage 2, verify coset ∈ Δ₀(N) |

## Decisions recorded

- **Route: twisted-action transport** (reviewer's path 1 / brief §8.2 option (ii)), chosen by user 2026-05-21.
- **Source ring: 𝕋(Γ₀(N))** (already CommRing). No genuine Γ₁(N) Hecke ring. (Confirms reviewer + brief Q3.)
- **Φ_χ is a χ-dependent representation** of the one algebra; χ-dependence explicit in the target type.
- Milestone re-scoped from "prove fresh equivariance" to "transport the existing canonical twisted ring hom" — materially smaller (days, not weeks).

## Revised plan (milestone = stage 1; bridge = stage 2)

Stage 1 — transport (this milestone):
1. Bridge the function-level `gamma0TwistedInvariantFunctionSubmodule k χ` to ModularForm-level `modFormCharSpace k χ` (forget/package directions, via the existing membership equivalence + Result 5.5 holomorphy/cusp-boundedness).
2. Restrict `twistedHeckeSlash_gen χ D` codomain to `modFormCharSpace k χ` (invariance = preserves_invariant DONE; holomorphy/cusp DONE for general D) → `End_ℂ(modFormCharSpace k χ)`.
3. Assemble `Φ_χ : 𝕋(Γ₀(N)) →+* End_ℂ(modFormCharSpace k χ)`; ℤ-linear + map_mul' transported from `twistedHeckeSumFunction_mul`.
4. Convention lemma: δ₀-weight upper-left-of-raw = diamond lower-right d on Δ₀(N) reps.

Stage 2 — bridge to concrete operators (generator route, reviewer's path 3):
- `Φ_χ(T(1,p)) = heckeT_p_all|_{χ-space}`; `Φ_χ(T(p,p)) = χ(p)·p^{k-1}·⟨p⟩`-type scalar; `U_p` for p∣N (verify coset ∈ Δ₀(N)).
- Derive commutativity/multiplicativity as ring corollaries; THEN collapse the standalone direct proofs.

## Changes rejected by user

- (none)

## Open questions remaining (reviewer didn't leave any unanswered)

- All of Q1–Q5 addressed. Sub-items folded into the plan: convention lemma (stage 1.4), bad-prime U_p (stage 2).

## Spike status

Step 1 (submodule bridge) being attempted as a concrete proof spike immediately after this record.
