# Decomposition: Option C-1 — Single-Prime Peel with Natural-Level F_q

**Date**: 2026-05-19
**Status**: Phase 1e adversarial
**Strategy**: Discharge the (4.6.14) sorry by exposing M7-sqfree's
internal V_q-preimage F_q at the correct natural level, enabling clean
M6(2) composition.

## Goal

For `Δ'` at level `Γ_1(l'·N)` with Coprime-`l'` Fourier vanishing,
show `a_m(slash_sum_at_l'N(Δ')) = 0` for `Coprime m l'`, by:

1. M6(1) bridge: `slash_sum_at_l'N(Δ') = slash_sum_at_(l'³·N)(Δ')` as
   functions (h_q at level Γ_1(l'·N), multiplier l'²).
2. M7-sqfree at level Γ_1(l'·N) with l = l': function identity
   `Δ'(z) = Σ_q V_q(F_q at NATURAL_q_level)(z)`.
3. M6(2) per q: `slash_sum_at_(l'³·N)(V_q(F_q at NATURAL_q_level))(z) =
   slash_sum_at_(NATURAL_q_level)(F_q)(q·z)`.
4. Take m-th Fourier coefficient: vanishes for Coprime m l'.

The KEY question: at what level `NATURAL_q_level` does M7-sqfree expose
F_q such that V_q(F_q) lives naturally at level `Γ_1(l'³·N)`?

**Answer**: `NATURAL_q_level = Γ_1(l'³·N/q)`. Then V_q sends
`Γ_1(l'³·N/q) → Γ_1(l'³·N/q · q) = Γ_1(l'³·N)` ✓ exactly matching M6(1)
bridge's target.

## CRITICAL FINDING — M7-sqfree's natural F_q level mismatch

Re-examination of M7-sqfree's inductive case (line 6119) shows:

```lean
rcases HeckeRing.GL2.conductor_theorem_dichotomy_cuspForm_strong
    q (N * q ^ 2) hq_dvd_Nq2 k χ_M φ h_form hh_form_char_χ_M ...
```

The dichotomy is at level `Γ_1(N · q²)` (the h_form level), NOT at level
`Γ_1(N · l²)`. So in the inductive case, F_q from M7-sqfree's internal
dichotomy is at level `Γ_1((N · q²)/q) = Γ_1(N · q)`.

For our use (N=l'·N, l=l', q ∈ l'.primeFactors), F_q is at level
`Γ_1((l'·N) · q) = Γ_1(l'·N · q)`, NOT at `Γ_1(l'³·N/q)`.

**Level discrepancy**: `l'·N · q` vs `l'³·N/q` — these differ by factor
`l'²/q² = (l'/q)²`. They're EQUAL only when `l' = q` (the base case, when
l' is a single prime).

For `1 < l'` (the case our helper actually addresses), they're DIFFERENT.

## Attacks on C-1

### Attack 1 — Counterexample search: does the natural-level claim hold?

For `l' = 2` (= q, base case): l' has one prime factor q. M7-sqfree's
base case (line 5879) applies dichotomy at level `Γ_1(N · l²) = Γ_1(N · q²)`,
giving F_q at level `Γ_1((N · q²)/q) = Γ_1(N · q) = Γ_1(N · l') = Γ_1(l' · N)`...

Wait, for l' = q and N_M7 = l'·N = q·N: the level Γ_1(N_M7 · l_M7²) =
Γ_1(q·N · q²) = Γ_1(N · q³). Dichotomy gives F_q at Γ_1((N·q³)/q) =
Γ_1(N·q²).

But the BASE CASE applies when l = q is a SINGLE prime. For our helper,
the base case would apply with l' = q (single prime). But the helper is
called only when `1 < l'`, which for squarefree l' could include l' = q
(single prime > 1).

Actually wait, `1 < l'` AND `l'` squarefree allows `l' = q` for any prime
q > 1. So the base case IS reachable.

For l' = q (single prime) base case:
- N_M7 = l'·N = q·N. l_M7 = l' = q.
- Dichotomy level: Γ_1(N_M7 · l_M7²) = Γ_1(q·N · q²) = Γ_1(N · q³).
- F_q at level Γ_1((N · q³)/q) = Γ_1(N · q²).
- We want F_q at Γ_1((l'·N · l'²)/q) = Γ_1((q·N · q²)/q) = Γ_1(N · q²). ✓ MATCHES.

For l' = q (single prime) base case, F_q IS at the right level Γ_1(l'³·N/q).

For l' composite (say l' = q · q' with q, q' distinct primes), inductive
case:
- N_M7 = l'·N = q·q'·N.
- Peeling q first: dichotomy on h_form at level Γ_1(N_M7 · q²) =
  Γ_1(q·q'·N · q²) = Γ_1(N · q³·q').
- F_q at level Γ_1((N · q³·q')/q) = Γ_1(N · q²·q').
- We want F_q at Γ_1(l'³·N/q) = Γ_1((q·q')³·N/q) = Γ_1(N · q²·q'³).
- LEVELS DIFFER by factor q'² (Γ_1(N·q²·q') vs Γ_1(N·q²·q'³)).

So for composite l', M7-sqfree's inductive natural F_q level is
`Γ_1(N · q²·q')` (when peeling q first), which is at a SMALLER subgroup
than the wanted `Γ_1(N · q²·q'³)` — i.e., the F_q is invariant under a
LARGER group than what M6(2) at level `Γ_1(l'³·N/q)` would need.

Wait, this is BACKWARDS from what I said before. Let me re-check.

Γ_1(N·q²·q') vs Γ_1(N·q²·q'³): which has more matrices?
- N·q²·q' is SMALLER than N·q²·q'³ (since q'² > 1).
- Γ_1(smaller M) is LARGER subgroup.
- So Γ_1(N·q²·q') is LARGER than Γ_1(N·q²·q'³).
- Hence F_q at Γ_1(N·q²·q') is invariant under MORE matrices than F_q at
  Γ_1(N·q²·q'³) would require.

So F_q at Γ_1(N·q²·q') HAS the invariance needed at Γ_1(N·q²·q'³) — by
RESTRICTION (going to a SMALLER subgroup is automatic for invariant
forms).

We can RESTRICT F_q from Γ_1(N·q²·q') to Γ_1(N·q²·q'³)! Then F_q at the
wanted level Γ_1(l'³·N/q) = Γ_1(N·q²·q'³).

Hmm, so actually M7-sqfree's natural F_q at Γ_1(N·q²·q') CAN be
restricted to Γ_1(N·q²·q'³) = Γ_1(l'³·N/q).

Let me verify in general. For l' composite with q ∈ l'.primeFactors,
M7-sqfree's natural F_q is at level Γ_1(l'·N · q) (peeling q first).

Wait wait — let me recompute. l' = q · q' (squarefree, two primes). M7-sqfree
with input level l'·N = q·q'·N. The inductive step peels one prime first;
let's say it peels q.

For the peel of q at level N_M7 = l'·N = q·q'·N:
- Inductive case (line 5990+): builds h_form at level Γ_1(N_M7 · q²) =
  Γ_1(q·q'·N · q²) = Γ_1(q³·q'·N).
- Dichotomy at level Γ_1(q³·q'·N) with divisor q: F_q at level
  Γ_1((q³·q'·N)/q) = Γ_1(q²·q'·N).

So F_q (natural, peeling q first) at level Γ_1(q²·q'·N) = Γ_1(l'·N · q)
(since l' = q·q' so l'·q = q²·q').

Wanted (for M6(2) composition at OUR base level l'·N): F_q at level
Γ_1((l'·N · l'²)/q) = Γ_1((q·q' · N · q²·q'²)/q) = Γ_1(q²·q'³·N) =
Γ_1(N · q² · q'³).

Natural Γ_1(l'·N · q) = Γ_1(q²·q'·N) = Γ_1(N · q² · q').

So natural Γ_1(N · q² · q') vs wanted Γ_1(N · q² · q'³): wanted has
extra q'² factor.

Γ_1(N · q² · q'³) is at HIGHER level (smaller subgroup) than Γ_1(N · q² · q').
So `Γ_1(N · q² · q'³) ⊂ Γ_1(N · q² · q')`.

For F_q at natural level Γ_1(N · q² · q') to also be at wanted level
Γ_1(N · q² · q'³): F_q is invariant under Γ_1(N · q² · q') (a LARGER
group), hence ALSO invariant under any subgroup including Γ_1(N · q² · q'³).

So F_q CAN be restricted from Γ_1(N · q² · q') to Γ_1(N · q² · q'³).
**This restriction is automatic** — invariance under a larger group
implies invariance under a smaller subgroup.

**Verdict on Attack 1**: The natural-level claim DOES hold in a refined
sense — M7-sqfree's natural F_q is at level Γ_1(l'·N · q) (or a multiple
thereof depending on peel order), which can be **restricted** to the
wanted level Γ_1(l'³·N/q). The restriction loses no information at the
function level.

### Attack 2 — Edge case: does the restriction preserve V_q(F_q)?

V_q(F_q at Γ_1(N · q² · q')) at level Γ_1((N · q² · q') · q) = Γ_1(N · q³ · q')
= Γ_1(l'³·N/q'²) (since l'³·N = q³·q'³·N).

Wanted: V_q(F_q at l'³·N/q) at level Γ_1((l'³·N/q) · q) = Γ_1(l'³·N).

So V_q(F_q at natural level Γ_1(N · q² · q')) is at level Γ_1(N · q³ · q'),
NOT Γ_1(l'³·N) = Γ_1(q³·q'³·N).

DIFFERENT levels: Γ_1(N · q³ · q') vs Γ_1(q³·q'³·N) (differ by q'²).

So V_q-lift of F_q at natural level is NOT at the same level as V_q-lift
of F_q-restricted-to-Γ_1(l'³·N/q).

**As functions on ℍ, are they the same?** V_q just multiplies z by q
(with scaling). The function (V_q F_q)(z) = (constant) · F_q(q·z). This
function value depends ONLY on F_q's function value at q·z — NOT on
which level F_q is bundled at.

So as FUNCTIONS on ℍ, V_q(F_q at natural) = V_q(F_q at wanted-restricted-level).

The level discrepancy is purely Lean type-level — at the function level, the V_q lifts
agree.

**Verdict on Attack 2**: SURVIVED — function identity holds despite
type-level differences.

### Attack 3 — Hypothesis test: does M6(2) compose at wanted levels?

M6(2) at smaller level Γ_1(l'³·N/q), l_M6 = q:
- Lifted level: q · (l'³·N/q) = l'³·N. ✓
- p ∣ N_M6 = l'³·N/q. Have p | N | l'³·N/q (since p coprime q, p | l'³·N and dividing by q preserves p|·). ✓
- NeZero(N_M6/p) = NeZero(l'³·N/(qp)). ✓
- l_M6 = q. Coprime p q ✓. q ∣ N_M6/p = l'³·N/(qp). Need q | l'³·N/(qp). q²·p | l'³·N iff q²·p | l'³·N iff (q²·p) divides (q³·q'³·N) — yes since q² | q³ and p | N. ✓
- Character bookkeeping: F_q must be in modFormCharSpace at level Γ_1(l'³·N/q). After restriction from natural level, the character composes with unitsMap.

**Verdict**: M6(2) composes IF F_q is in modFormCharSpace at Γ_1(l'³·N/q).
The restriction from natural level changes the character to the
composed version — needs verification.

### Attack 4 — Source-drift: does Miyake's proof match this?

Miyake p. 161-162 (per project docstring transcription):
> "slash_sum_lifted(h)(z) = Σ_{q|l'} (slash_sum_deeper(h_q))(qz)"

Where "deeper" = at level Γ_1(l'³·N) (where M7-sqfree's output g_q lives,
post-restriction). So Miyake's identity uses the UNIFORM output level
Γ_1(l'³·N).

Our analysis: slash_sum_at_l'³·N(h_q)(qz) — but h_q is at level l'³·N,
NOT at Γ_1(l'³·N/q). So Miyake's "slash_sum_deeper(h_q)" is at level
l'³·N, applied to h_q at level l'³·N.

But for M6(2) to apply at level l'³·N (smaller side) with l_M6 = q,
lifted = q · l'³·N. Hmm that's at level q · l'³·N, NOT l'³·N. So
slash_sum_at_l'³·N applied to V_q(...) doesn't directly match M6(2)'s
output.

Hmm. So Miyake's identity (slash_sum_deeper(h_q))(qz) actually means
slash_sum_at_l'³·N applied to h_q (at level l'³·N), then evaluated at qz.

By M6(2) with smaller level Γ_1(l'³·N), l_M6 = q:
slash_sum_at_(q · l'³·N)(V_q(h_q at l'³·N))(z) = slash_sum_at_l'³·N(h_q)(qz).

So Miyake's RHS = slash_sum_at_(q · l'³·N)(V_q(h_q at l'³·N))(z).

For this to equal slash_sum_at_l'³·N(V_q(h_q))(z) (what we get from
linearity after substituting h = Σ V_q(h_q) into slash_sum_at_l'³·N(h)):
we'd need slash_sum at level l'³·N and at level q · l'³·N to agree on
V_q(h_q). By M6(1), this requires V_q(h_q) at level Γ_1(l'³·N) (smaller).

V_q(h_q at l'³·N) is at level Γ_1(q · l'³·N) (HIGHER). For it to also be
at level Γ_1(l'³·N), need more invariance.

**This is the same gap we kept hitting!**

UNLESS h_q's NATURAL level is Γ_1(l'³·N/q) (not l'³·N), in which case
V_q(h_q at l'³·N/q) is naturally at level Γ_1(l'³·N) ✓ — which is what
my original C-1 plan claimed.

But per M7-sqfree's project formalization, the natural level for the
INDUCTIVE case is Γ_1(l'·N · q), NOT Γ_1(l'³·N/q).

**Conclusion of Attack 4**: Miyake's argument is mathematically sound,
but requires F_q at level Γ_1(l'³·N/q) — which is NOT what M7-sqfree's
inductive proof exposes. The project's M7-sqfree internal level
(`l'·N · q` for inductive case) differs from what Miyake's argument
formally needs (`l'³·N/q`).

### Attack 5 — Discharge attack: can C-1 be discharged at all?

To make C-1 work, we need F_q at level **Γ_1(l'³·N/q)**, not at M7-sqfree's
inductive natural level Γ_1(l'·N · q).

Two approaches:
- (C-1a) **Modify M7-sqfree's inductive proof** to do the dichotomy at
  level Γ_1(l'³·N) (the final uniform level) instead of at level
  Γ_1((l'·N) · q²). This requires reorganizing M7-sqfree's induction.
- (C-1b) **Use M7-sqfree's restricted output g_q at level Γ_1(l'³·N)**
  directly. Apply 4.6.4 (dichotomy) to g_q at level Γ_1(l'³·N) with
  divisor q to get F_q at level Γ_1(l'³·N/q). For this to apply, g_q
  must be q-supported (a_n(g_q) = 0 for ¬q|n).

**Is g_q q-supported?** Per M7-sqfree's qExp identity:
`a_n(f) = Σ_{q∣l, q∣n} a_{n/q}(g_q)`.

This says f decomposes into V_q-shifted g_q's. But the qExp of g_q
itself is NOT directly specified — only the qExp of `V_q(g_q)` (which
shifts to f's coefficients).

For g_q itself: `a_m(g_q)` is determined by `f(z) = Σ_q g_q(qz)` (Miyake
function-level identity). Specifically, `a_m(g_q)` = `a_{qm}(f)` for some
range. Actually it's more subtle due to overlaps when multiple primes
of l divide.

**Critical**: g_q's q-expansion in M7-sqfree DOESN'T directly satisfy
"a_n(g_q) = 0 for ¬q|n". It satisfies a different identity (the
inclusion-exclusion-like sum over q | l, q | n).

So g_q is NOT necessarily q-supported. Applying dichotomy 4.6.4 to g_q
with divisor q requires q-supportedness, which fails in general.

**Verdict on Attack 5**: C-1b FAILS — g_q is not q-supported, so we
can't apply 4.6.4 to it at level Γ_1(l'³·N) to extract F_q.

C-1a (restructure M7-sqfree's induction) is the only remaining path,
and it requires substantial modification to the existing M7-sqfree proof.

## Summary verdict on Option C-1

**Both sub-options fail**:
- C-1a requires restructuring M7-sqfree's induction to do dichotomies at
  the uniform output level — a substantial proof reorganization.
- C-1b doesn't work because M7-sqfree's `g_q` is not q-supported (it's
  the V_q-preimage of an inclusion-exclusion component, not a clean
  q-supported form).

## Confidence gate status

1. ❌ L1 (single-prime peel construction) BLOCKED — natural-level F_q
   from M7-sqfree is at a different level than what M6(2) needs.
2. N/A — no Lean skeleton (would not have the right shape).
3. ✅ Source quotes available.
4. ❌ Attack 4 (source drift) and Attack 5 (discharge) both surfaced
   real obstacles.
5. ✅ Prior B2 log clean.
6. ❌ Tree mirroring requires M7-sqfree to expose levels it doesn't.

## Revised recommendation

After three iterations of /develop --decompose (Options A, B, C-1),
every path has surfaced obstacles that require non-trivial new
infrastructure. The (4.6.14) Fourier-vanishing sorry is **genuinely
hard** to formalize from existing project lemmas.

The cleanest of the three paths is **C-1a** (restructure M7-sqfree),
but this requires modifying a 600+ line proof that's already
checkpointed and working. The risk of breaking downstream consumers is
real.

**Alternative recommendation**: Step back and consider whether the
M8 chain itself (which routes through this helper) is the right
architecture. The project's file docstrings suggest that the
intended-but-unimplemented routes use either:
- D-S §5.7.1 / Miyake 4.6.5 (U_p-eigenvalue route) — `mainLemma_charSpace_composite_via_Up`,
- D-S §5.7.2 (Petersson / Atkin-Lehner-Li orthogonal decomposition) —
  `cuspFormsNew_orthogonal_cuspFormsOld`,
- Möbius sieve — `cuspFormsOld_of_coprime_coeff_vanishing_via_Mobius`.

None of these are formalized. Each is a substantial project.

The pragmatic options are:
- (P-1) Accept the sorry, document the (4.6.14) Fourier vanishing
  as an axiom-equivalent gap, move on with the rest of SMO.
- (P-2) Restructure M7-sqfree (C-1a) — the cleanest mathematical fix
  but the most invasive.
- (P-3) Develop the same-level diamond-character infrastructure for
  D-S §5.7's Atkin-Lehner-Li route — long-term cleanest but
  substantial new development.

The user's choice should be guided by their priorities (time-to-close
SMO vs. long-term code health).
