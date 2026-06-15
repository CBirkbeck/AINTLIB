# Reviewer reply — 2026-05-26 (QF keystone route choice)

*Verbatim record of the reviewer's reply to `brief.md` (the same reviewer as the
prior Silverman round-trips). Reproduced as received; minor LaTeX/markdown paste
artifacts preserved.*

## Verdict

My recommendation has **not changed**: commit to **Route 1, Pic⁰ functoriality /
restricted dual additivity**, and stop trying to finish the explicit coordinate route as
the primary path. The new shipped facts — concrete V, point-map trace identity, and
composition identities — are useful, but they do not remove the true bottleneck:

  (rπ − s)^ = rV − s.

They mainly show that you are very close **provided** you can move from point-map-level
identities to genuine isogeny/pullback identities. Your own brief identifies exactly this:
degree is defined from pullbacks, not point maps, and equal point maps do not automatically
give equal degrees in the current formalisation.

So the project should split effort as follows:

1. **Primary mathematical route:** Route 1, restricted Pic⁰/dual-additivity.
2. **High-leverage infrastructure lemma:** genuine isogenies are determined by their
   geometric point-map.
3. **Do not continue Route 3 as primary:** its Wall A/Wall B issues are genuine, not
   tactical.
4. **Do not treat Route 2 as a separate shortcut:** without dual identification it only
   gives an absolute-value statement, not the signed degree identity.

## Q1. Which route should be primary?

Choose **Route 1: Pic⁰ functoriality**, at least restricted to the Frobenius plane
ℤπ + ℤ. The target is not just a composition identity; the proof needs the **dual
identification** (rπ − s)^ = rV − s. Once known, everything is uniform:
(rV − s)(rπ − s) = [qr² − trs + s²], and because (rV − s) is the actual dual of (rπ − s)
this equals [deg(rπ − s)]; the sign is then fixed automatically and
qr² − trs + s² = deg(rπ − s) ≥ 0. Route 3 is now clearly the wrong primary path (three
serious obstructions; independent passes converged on "use the abstract/dual route").
Route 2 is only useful if upgraded into Route 1. **Route 1 remains the right route**; the
shipped V and point-map trace identity reduce remaining work but do not change the strategy.

## Q2. Is there a simpler path to Q(r,s) ≥ 0?

Not a substantially simpler one.
- **Parallelogram law for degree** is not independent — it is essentially III.6.3 in
  another language; proving it without duality reintroduces the same machinery.
- **Point-counting** deg(rπ−s) = #ker(rπ−s) works only for separable members, needs
  kernel-size control for a two-parameter family, and is not a short path to the exact
  polynomial; fails to handle inseparable/zero cases uniformly.
- **Weil pairing / torsion determinant** is valid but a major new branch (Weil pairing,
  E[N] ≅ (ℤ/N)², determinant–degree congruence, congruence-to-integer lifting); likely
  larger than finishing Pic⁰ unless that stack already exists.
- **Cayley–Hamilton / composition identity** gives only deg(rV−s)deg(rπ−s) = Q², hence at
  best an absolute-value conclusion. No: no simpler route avoids restricted dual
  additivity; torsion-determinant is the only serious alternative and likely heavier.

## Q3. Is Route 2's sign concern correct?

Yes. From (rV−s)(rπ−s) = [Q], degree multiplicativity gives deg(rV−s)deg(rπ−s) = Q²; with
deg(rV−s)=deg(rπ−s) this gives deg(rπ−s) = |Q|, which does **not** prove Q ≥ 0. The sign is
fixed only when rV−s is identified as the **actual dual** of rπ−s, giving
(rV−s)(rπ−s) = [deg(rπ−s)] and hence Q = deg(rπ−s) (not merely |Q|). Restricted dual
additivity is the sign-carrying content. There is no clean sign-closure from "q > 0" or
continuity alone — the continuity/density argument works only **after** nonnegativity on
integer pairs is known.

## Q4. Should you invest in "a genuine isogeny is determined by its point-map"?

Yes — high-value structural lemma. Safe version: if φ, ψ : E → E′ are **genuine** isogeny
records with compatible coordinate-ring witnesses and agree on E(K̄), then their pullbacks
agree, hence degrees agree. Must be restricted to genuine isogenies (placeholders are the
counterexamples). It would collapse much of Wall B (promote π + V = [t] and
(rV−s)(rπ−s) = [Q] to pullback/isogeny level for genuine maps). But it does **not** close
the theorem alone — the irreducible residue remains (rπ − s)^ = rV − s. Make it a priority
in parallel, not a substitute. Suggested Lean shape:
`genuine_isogeny_ext_of_pointMap_eq (φ ψ : Isogeny E E') (hφ : φ.IsGenuine) (hψ : ψ.IsGenuine)
(hpt : ∀ P, φ.toPointMap P = ψ.toPointMap P) : φ.pullback = ψ.pullback`, then derive
`degree_eq`. Likely reusable far beyond Hasse.

## Q5. Where should ordinary/supersingular be absorbed?

In **Verschiebung existence / inseparability-degree infrastructure**, not in the Hasse QF
proof. Routes 1/2 avoid the case split at proof level because duality is uniform
(V = π̂, Vπ = πV = [q], (rπ−s)^ = rV−s); the distinction stays buried in V's existence and
properties (already constructed). Route 3 forces it into the V-side pole order (Wall A) and
division-polynomial degrees — another reason it is unattractive. Do not build a
character-aware Wall A unless forced.

## Additional correction: Wall A's −2 claim

Cautious about the blanket claim ord_∞((rV−s)*x) = −2. The general local formula is
ord_O(α*x) = −2·e_α(O), with e_α(O) the ramification/inseparable contribution at O (tied to
deg_i(α)). So −2 holds when α is separable at O, but is not general-purpose for arbitrary
rV−s. If a ticket asserts −2 for all (r,s) it should be audited. Another reason not to make
Route 3 primary.

## Recommended execution plan

- **Primary W4 route:** restricted Pic⁰ / dual-additivity on ℤπ + ℤ.
- **Secondary formalisation shortcut:** genuine-isogeny extensionality by point-map.
- **Do not continue explicit coordinate Wall A/B as primary.**

Near-term: (1) prove genuine-isogeny extensionality (removes Wall-B friction); (2) prove
restricted dual additivity (rπ−s)^ = rV−s via Pic⁰ functoriality or a narrowly-targeted
dual-additivity theorem on the Frobenius plane; (3) use shipped V and point-map trace
identity as inputs only (do not mistake them for the full isogeny-level trace identity
unless extensionality upgrades them); (4) keep Route 3 only as a fallback for specific local
computations.

What not to do: don't finish the V-side division-polynomial pole-order as the main route;
don't rely on the abstract degree-square route without the dual identification; don't add
ordinary/supersingular case splits to the final QF proof.

## Bottom line

The earlier Pic⁰ route remains the right one. The new shipped facts reduce the amount of
work but do not eliminate the central theorem: restricted dual additivity on ℤπ + ℤ. The
most promising optimisation is the structural lemma "genuine isogeny determined by
geometric point-map", which collapses the formal pullback gap, leaving the true core
exactly where it belongs: (rπ − s)^ = rV − s. Once proved, the Hasse quadratic-form witness
should close cleanly and uniformly, including supersingular and characteristic-divisible
cases.
