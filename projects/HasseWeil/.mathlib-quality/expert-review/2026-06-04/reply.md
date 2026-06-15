# Reviewer reply — round 23 (2026-06-04)

## Verdict
Take **Route B**. There is a very clean EXPLICIT proof; no density, CRT, pigeonhole, or interval argument.

If `Q(r,s)=qr²−trs+s²` is nonnegative for all pairs with `p∤r` and `p∤s`, then `t²≤4q`. Contrapositive has an explicit prime-to-p negative pair: if `Δ:=t²−4q>0`, choose a positive integer `m` divisible by `p` and large, set
`r = mt+1`, `s = 2mq+1`.
Then `r≡1`, `s≡1 (mod p)`, so `p∤r,s`. Direct calc:
`Q(mt+1, 2mq+1) = (4q−t²)(qm²+m) + (q−t+1) = −Δ(qm²+m) + (q−t+1)`,
negative for large m. Contradiction. Much smaller/cleaner than Route A.

## Q1 — clean low-machinery proof (formalisation-ready)
Lemma: q>0, p prime, t∈ℤ; if Q(r,s)=qr²−trs+s²≥0 for all r,s with p∤r ∧ p∤s, then t²≤4q.
Proof (contrapositive): assume Δ=t²−4q>0. Let C=q−t+1. Choose m a positive multiple of p with Δ(qm²+m)>C — e.g. **m = p(|C|+1)** (avoids asymptotics: p≥2 ⟹ m≥|C|+1; q≥1 ⟹ qm²+m≥|C|+1; Δ≥1 ⟹ Δ(qm²+m)>|C|≥C). Set r=mt+1, s=2mq+1. Since p∣m: r≡1, s≡1 mod p ⟹ p∤r, p∤s. Compute:
`Q(mt+1,2mq+1) = (4q−t²)(qm²+m)+(q−t+1) = −Δ(qm²+m)+C < 0`. Contradiction.
Key `ring` lemma: `Q q t (m*t+1) (2*m*q+1) = (4*q−t^2)*(q*m^2+m) + (q−t+1)`. Then rewrite `4q−t²=−Δ`.
Modular step: p∣m, r−mt=1, s−2mq=1; if p∣r then p∣(r−mt)=1, impossible. Same for s.
This is one explicit family approaching the negative ray (t,2q) (`Q(t,2q)=q(4q−t²)<0`); perturbation (+1,+1) forces both coords ≡1 mod p. No topology/density/CRT. Likely far under 150–250 LOC.

Lean statement sketch:
`lemma qf_nonneg_prime_to_p_implies_discriminant_nonpos {p:ℕ}(hp:p.Prime){q:ℤ}(hq:0<q){t:ℤ}(hQ:∀ r s:ℤ, ¬(p:ℤ)∣r → ¬(p:ℤ)∣s → 0 ≤ Q q t r s) : t^2 ≤ 4*q`
+ `lemma Q_special (q t m:ℤ): Q q t (m*t+1)(2*m*q+1) = (4*q−t^2)*(q*m^2+m)+(q−t+1) := by ring`.

## Q2 — Route B complete for Hasse? YES.
Nonnegativity on {p∤r ∧ p∤s} already forces t²≤4q. You do NOT need Q≥0 for every pair — only the discriminant bound. Complete. No problematic edge cases: t=0 ⟹ t²≤4q immediate (contrapositive never triggers); p∣q fine (m itself divisible by p, so s=2mq+1≡1 mod p — don't even need p∣q); p=2 fine (r≡s≡1 mod 2); negative t fine.

## Q3 — Route A differential shortcut: CAREFUL (largely circular).
An INSEPARABLE isogeny does NOT generally have ord_O(α*x)=−2: Frobenius gives ord_O(π*x)=ord_O(x^q)=−2q. What is true: the WHOLE map rπ−s is separable when p∤s (omega coeff −s≠0), so once constructed it's unramified at O and ord_O(φ*x)=−2 (differential proof: ω nonvanishing at O, φ*ω=a_φ ω, a_φ=−s≠0 ⟹ dφ_O≠0 ⟹ e_O=1 ⟹ double pole). BUT this shortens A only if the genuine comorphism already exists; if the −2 pole is needed to construct/show-well-defined the addition comorphism, it's CIRCULAR. A non-circular A shortcut: prove the formal-local `(rπ−s)*t = −s·t + O(t²)` (unit linear coeff) directly — avoids inseparable division-poly degree analysis but still more geometric than B. Given B, don't spend effort on A for Hasse.

## Q4 — third route?
B IS the third route in practice (bypasses the geometric p∣r case). No better algebraic identity for p∣r∧p∤s specifically; relating Q(r,s) to Q(r+1,s) by convexity doesn't give reliable integral sign transfer. Don't pursue a separate third route.

## Q5 — which route + is B honest? Take B. It IS honest.
The final theorem is Hasse's inequality, not the full Silverman III.6.3 degree formula for every (r,s). Route 2A already uses #ker(rπ−s) (cardinality) not the geometric degree — a deliberate simplification that eliminated the `#ker=deg` hard fact. Route B continues in that spirit: prove just enough nonnegativity to force the discriminant bound. It leaves a STRONGER theorem unproved (the scaling/degree for p∣r∧p∤s) but NO gap in the Hasse bound. The full `deg(rπ−s)=qr²−trs+s² ∀r,s` is a valuable POST-HASSE strengthening (Route A / full QF), not the last blocker.

Recommended implementation:
1. Add `qf_nonneg_prime_to_p_coords_implies_hasse`.
2. Change the reduction so the pencil scaling leaf is only requested under p∤r ∧ p∤s.
3. Remove the p∣r, p∤s geometric `sorry` from the bound path.
4. Keep the Route A ticket as future enhancement "full QF / all pencil members", not "Hasse blocker".
First genuinely axiom-clean Hasse theorem with minimal risk.
