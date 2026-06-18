# Reviewer reply — round 2 (2026-05-26): QF fork resolved → B narrow + C supporting

*Verbatim record of the reviewer's round-2 reply to brief.md. Same reviewer as round 1.*

## Verdict

The "Pic⁰ dual is degree-blind" finding is serious but does NOT move from the Pic⁰ route to
pure K̄-extensionality. Revised recommendation:

> **Complete the Pic⁰ route honestly enough to produce a genuine degree-bearing comorphism,
> and separately prove the K̄-point-map extensionality lemma as a high-leverage formalisation
> shortcut.**

Extensionality can certify equality between ALREADY-genuine morphisms; it cannot turn a
placeholder-pullback isogeny into a degree-bearing one. The missing object is not just an
equality proof — it is a real degree-bearing morphism.

## Q1 — B or C? Favor **B, narrowed.**

Pure C only applies once both sides are already genuine isogenies with pullbacks tied to
their point-maps; it cannot prove a placeholder Pic⁰ dual has the correct pullback. B should
NOT build an enormous Picard-functor comorphism stack — the target is the narrow
degree-bearing theorem: for β = rπ−s, construct a genuine β_dual (real pullback) with
β_dual∘β = [N] at the function-field/degree level (= the named pivot
`genuineIsogSmulSub_pivot_witness`). Use B primary, C supporting (not a replacement).

## Q2 — degree-only route avoiding the genuine dual? Not lighter.

- **D (deg = deg_s·deg_i):** avoids duals syntactically but creates two new hard problems —
  #ker(rπ−s)(K̄) for all (r,s), and the inseparable degree for all (r,s). Likely harder than
  restricted dual additivity. Not a good shortcut.
- **Weil pairing / torsion determinant:** valid, avoids the dual pullback, but needs
  E[N]≅(ℤ/N)², Weil pairing, determinant-degree identity, trace comparison,
  congruence-to-integer lifting — a major new branch unless that stack already exists.
- **Height/Rosati:** essentially another form of dual-isogeny theory; not shorter.
- Net: no evidently lighter degree-only route.

## Q3 — Is C the same as B? Overlap, not identity.

C gives: φ_K̄ = ψ_K̄ on E(K̄) ⟹ φ* = ψ* for GENUINE morphisms (structural extensionality, not
Pic⁰-specific; collapses Wall B by upgrading point-map identities to pullback identities once
both sides are genuine). C does NOT construct the genuine pullback of the Pic⁰ dual. B
constructs genuine morphisms/comorphisms; C proves extensional equality between them. If the
only construction of rV−s as a genuine morphism is Pic⁰ functoriality, then C depends on B's
output in practice.

## Q4 — Is the genuine dual pullback irreducible? For the Silverman III.6 route, YES.

The keystone is (rπ−s)^ = rV−s. Once known at the degree-bearing level,
(rV−s)(rπ−s) = (rπ−s)^∘(rπ−s) = [deg(rπ−s)], and ring algebra with Vπ=[q], V+π=[t] gives
= [qr²−trs+s²], hence deg(rπ−s) = qr²−trs+s² ≥ 0. Without the genuine dual identification the
composition square only gives deg(rV−s)·deg(rπ−s) = N² (an absolute-value phenomenon), not the
signed equality. You can avoid it only by switching to a different large theory (Weil pairing
/ torsion determinant).

## Strategic recommendation

- **Primary: B, completed narrowly.** Deliverable = `genuineIsogSmulSub_pivot_witness` for
  β = rπ−s: a genuine β_dual with real pullback and β_dual∘β = [N] at the function-field level.
  NOT all Picard functor theory.
- **Parallel structural lemma: C** = `genuine_isogeny_ext_of_geometric_pointMap_eq` —
  supporting infrastructure (shortens the pullback-equality proof once genuine maps exist),
  not the main route.
- **Do not pursue D as primary** (deg_s·deg_i is a detour).
- **Do not revive explicit-coordinate Route 3** (V-side pole-order obstruction is real).

## Concrete next target

```
theorem frobeniusPlane_genuine_dual (r s : ℤ) :
    ∃ β βdual : Isogeny E E,
      β.toPointMap = r • π.toPointMap - s • id ∧
      βdual.toPointMap = r • V.toPointMap - s • id ∧
      β.IsGenuine ∧ βdual.IsGenuine ∧
      βdual.comp β = mulByInt E (q*r^2 - t*r*s + s^2)
```
then extract `degree β = q*r^2 − t*r*s + s^2`. If β = rπ−s is already genuine, only
construct/repair βdual.

## Bottom line

The Pic⁰ dual being degree-blind does not make K̄-extensionality the primary route; it shows
the Pic⁰ route must be completed at the comorphism / genuine-pullback level. Use
K̄-extensionality as an accelerator once genuine candidates exist. The irreducible Hasse
keystone remains the genuine restricted dual additivity (rπ−s)^ = rV−s at the level where
degree is defined.
