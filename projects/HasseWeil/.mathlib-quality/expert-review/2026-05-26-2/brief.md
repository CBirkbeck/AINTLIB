# Review brief (round 2) — Hasse bound: the Pic⁰ dual is degree-blind

*Prepared 2026-05-26 for the same reviewer. Follows round 1 (your "commit to Pic⁰ /
restricted dual additivity; the structural extensionality lemma is the high-leverage
shortcut" reply). Short and sharp — one finding, one fork.*

## 0. Why I'm back so soon

We committed to your Pic⁰ route and started executing. Two facts you flagged came back
**positive**, and one came back as a **wall your steer didn't anticipate** — and it bears
directly on the Pic⁰ recommendation. I want your read before we sink weeks into one of two
substantial completions.

## 1. What's now confirmed (good news)

- **V = π̂ exists as a genuine isogeny, axiom-clean.** `verschiebung_dual_exists` checks out:
  `∃ V, IsDualOf V π`, with `V∘π = π∘V = [q]`, depending only on the standard axioms. So the
  Verschiebung-dual existence is *not* the bottleneck.
- **Pic⁰(E) ≅ E is shipped, axiom-clean** (over an algebraically closed base, with the usual
  `char ≠ 2,3` and Dedekind/integrally-closed coordinate ring), with a base-change form. The
  Abel–Jacobi isomorphism and the Pic⁰ pushforward/pullback functoriality (including the
  diagram `φ_*(κ P) = κ(φ P)`) are all in place.
- **The trace identity `π + V = [t]` holds at the point-map level** (a Lagrange argument over
  𝔽_q), and the hom-level composition `(rV − s)∘(rπ − s) = [N]`, `N = q·r² − t·r·s + s²`, is
  shipped.

So the keystone `qf_nonneg` reduces, as you said, to the dual identification on the plane.
We pinned it to a single named leaf.

## 2. The wall: our "dual isogeny" carries data the point-map can't recover, and the Pic⁰ dual fills it with a placeholder

Our formalised isogeny is a **pair**: a function-field pullback `φ*: K(E) → K(E)` **and** a
point-map `φ: E → E`, carried as independent data. Crucially **`deg φ := dim_{φ*K(E)} K(E)`
is read off the *pullback*, not the point-map.** Over a finite field the point-map fixes only
the *separable* degree (the kernel size over K̄); since `rπ − s` is generically
**inseparable**, its point-map does **not** determine its degree.

Now the catch. The shipped "dual via Pic⁰" construction produces the dual isogeny with a
**placeholder pullback** — it literally reuses `α`'s own pullback rather than the genuine
comorphism of the Pic⁰ map. So the Pic⁰-constructed dual is **degree-blind**: its `deg`
(finrank of the placeholder) is not `deg α`. The whole Pic⁰ stack lives at the
point-map/divisor level; it never builds the genuine function-field comorphism of the dual.

Concretely: the lemma actually on the Hasse critical path — `deg(rπ − s) = N` — is **still
open even though V, the trace identity, the V-side chain, and the entire Pic⁰ stack are all
in scope**. The gap is irreducible against the current codebase, not an artifact of import
order. The keystone is exactly:

> **`genuineIsogSmulSub_pivot_witness`** — for `β = rπ − s` there is a *genuine* isogeny
> `β_dual` (with a real pullback) such that `β_dual ∘ β = [N]` **at the function-field /
> degree-bearing level**, with `deg β > 0` and `N ≠ 0`. (Silverman III.6.2(b/c).)

Neither of the two routes we have provides this: the explicit-coordinate construction of
`rV − s` is blocked by the V-side pole-order obstruction (the 3-way tie at the dominant order
you cautioned about — your `ord_O(α*x) = −2·e_α(O)` correction is exactly the relevant
subtlety), and the shipped Pic⁰ dual is the placeholder above.

## 3. The fork

To produce the genuine dual pullback we see three options:

- **(B) Complete the Pic⁰ route honestly:** build the genuine function-field comorphism of
  the Pic⁰ functorial dual (upgrade the placeholder to the real pullback). This is the
  faithful version of your recommendation; cost is the AG of "the Pic⁰ map of a curve
  morphism is the comorphism on function fields."
- **(C) K̄-extensionality + degree descent:** over the algebraic closure an isogeny is
  determined by its geometric point-map (an isogeny vanishing on the infinite group `E(K̄)`
  is `0`), so equal K̄-point-maps force equal genuine pullbacks; lift `(rV−s)∘(rπ−s) = [N]`
  to `E(K̄)`, conclude the genuine pullback identity, and descend the degree via base-change
  invariance (which we have). Our worry: the "equal-on-E(K̄) ⟹ equal pullback" step, given
  pullback and point-map are independent data, may have to be *restricted to genuine
  isogenies / tie the pullback to the point-map via the comorphism* — which seems to
  reintroduce (B)'s content.
- **(D) Avoid the genuine dual entirely:** compute `deg(rπ−s) = sep-deg · insep-deg`, with
  `sep-deg = #ker(rπ−s)(K̄)` from the point-map and `insep-deg` a `p`-power from the
  inseparability/invariant-differential structure (we have `ω`-pullback-coefficient
  infrastructure and the `[p] = V∘π` factorization). This sidesteps the dual but needs a
  two-parameter kernel count plus the inseparable-degree bookkeeping.

## 4. Questions

**Q1.** Given that the shipped Pic⁰ functorial dual is **degree-blind (placeholder
pullback)** and the degree lives in the pullback, do you still favor completing the Pic⁰
comorphism (B), or does this move you to the K̄-extensionality route (C)?

**Q2.** Is there a route to `deg(rπ−s) = N` that **avoids constructing the genuine dual
pullback** — e.g. the `sep-deg · insep-deg` factorization (D), or another standard device
(Weil pairing determinant, height pairing) — that you'd expect to be *lighter* than building
the genuine dual? We'd rather not build the comorphism if a degree-only route exists.

**Q3.** For (C): is "an isogeny is determined by its geometric point-map, hence its degree
is" the right anchor lemma, and does tying it to *genuine* isogenies (pullback = comorphism
of the point-map) collapse it back into (B)? In other words, are (B) and (C) the same
mathematical content wearing different clothes?

**Q4.** Sanity check on the whole reduction: is the genuine dual pullback of `rπ−s`
**genuinely the irreducible §5.4 content**, i.e. is there *no* way to get the degree
quadratic form without it? If it is irreducible, we'll build it; we just want to be sure
before committing.

## 5. Status metadata

- The bound is assembled and sorry-free downstream of two `HasseWitnesses` leaves.
- **V.1.3 (point-count) witness:** two of its ramification bridges shipped axiom-clean this
  session (the kernel-prime is prime; it lies over `(x)`); the rest is bounded substrate (a
  curve-valuation ↔ Dedekind ramification-index bridge, an inertia-degree-1 residue
  computation, a bijection, an assembly) — no fork, proceeding in parallel.
- **III.6.3 (`qf_nonneg`) witness:** pinned to `genuineIsogSmulSub_pivot_witness` above —
  this brief's subject.
- References as round 1: Silverman III.4, III.6.1–6.3, V.1.1–1.3; Sutherland Lecture 7.
