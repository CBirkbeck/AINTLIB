# Review brief — Hasse bound for E/𝔽_q: the degree-quadratic-form keystone

*Prepared 2026-05-26. Continuation of the earlier round-trips with you (the
Frobenius-plane short-circuit rejection and the Pic⁰ recommendation). Self-contained,
but I lean on our shared framing where it saves space.*

---

## 0. One-paragraph ask

We have driven the full Hasse bound down to a single remaining piece of genuine
mathematics, and we have three candidate routes to it. We want your steer on **which
route to commit to** — or whether there is a **simpler path we are not seeing**. The
piece is the restricted dual-additivity / degree-quadratic-form keystone you flagged last
round as the true bottleneck. Since then several supporting facts have shipped (the
Verschiebung as the dual of Frobenius; the trace identity at the level of point-maps; the
degree-composition identity modulo dual existence), and we want to know whether that
changes your earlier "Pic⁰ if you want reusable infrastructure, and the direct
degree-computation is not a shorter route" verdict.

---

## 1. Goal and where it now stands

Target: the unconditional bound `|#E(𝔽_q) − q − 1| ≤ 2√q` for an elliptic curve E over a
finite field 𝔽_q, with `q = #𝔽_q`, with no per-characteristic restrictions and no
unproven inputs.

Write π for the q-power Frobenius endomorphism, `t = tr(π)` (so `#E(𝔽_q) = q + 1 − t`),
and `[n]` for multiplication-by-n. The bound is equivalent to `t² ≤ 4q`.

The proof is fully assembled and **reduces to exactly two facts**, both stated for the
genuine isogeny `1 − π`:

- **(V.1.3)** `deg_s(1 − π) = #E(𝔽_q)` — the separable degree of `1 − π` equals the point
  count. **In hand**: decomposed into a ramification-at-infinity bridge that we have
  verified dispatchable (details in §5; not the subject of this brief).
- **(III.6.3)** `q·r² − t·r·s + s² ≥ 0` for all `r, s ∈ ℤ` — the degree map restricted to
  the plane `ℤπ + ℤ·1 ⊂ End(E)` is a non-negative binary quadratic form. **This is the
  open strategic question.**

Everything downstream of these two facts is proven and axiom-clean: the discriminant step
`(non-negative form) ⟹ t² ≤ 4q`, the conversion to `|t| ≤ 2√q`, the point-count identity
`#E(𝔽_q) = q + 1 − t` via the kernel-degree route, separability of `1 − π` (from
`ω(1 − π) = 1` by an explicit Kähler-differential computation), and finite-dimensionality.

So the brief is entirely about how to prove the non-negativity of the binary form
`Q(r,s) = q·r² − t·r·s + s²`.

---

## 2. Setting — one structural point you need

Our formalised "isogeny" object carries **two pieces of data simultaneously**:

- a pullback algebra-homomorphism on function fields `K(E) → K(E)`, and
- the induced homomorphism on points (the "point-map").

Crucially, **degree is defined as the field-extension degree of the pullback**
(`deg(φ) = [K(E) : φ*K(E)]`), *not* read off from the point-map. This design choice is the
source of all the friction below. In ordinary mathematics an isogeny is determined by its
point-map and the degree is a function of it; in our setup the two are a priori
independent, and several historically-convenient isogenies were built with a *placeholder*
pullback (the identity map, hence spurious degree 1). The live development has migrated the
Hasse-critical isogenies (`1 − π`, and `rπ − s`) to **genuine** pullbacks built from the
Weierstrass addition formulas, but the placeholder legacy is why "equal point-maps" does
**not** give us "equal degrees" for free — see Wall B in §5.

Notation: `V = π̂` is the Verschiebung (the dual of π), with `V∘π = π∘V = [q]`. The trace
is `t = tr(π)`, and `tr(V) = tr(π) = t`. `deg_s`, `deg_i` are separable / inseparable
degree; `deg = deg_s · deg_i`.

---

## 3. Why the keystone is `(rπ − s)^ = rV − s`

`Q(r,s) ≥ 0` is immediate **once** `Q(r,s) = deg(rπ − s)`, because a degree is a
non-negative integer. So the whole question is the **degree identity**
`deg(rπ − s) = q·r² − t·r·s + s²`.

The classical route (Silverman III.6.1–6.3): the dual satisfies `φ̂∘φ = [deg φ]`, and the
map `φ ↦ φ̂` is **additive** on End(E). Restricting additivity to the plane,
`(rπ − s)^ = r·π̂ − s·1̂ = rV − s`. Then

> `(rV − s)∘(rπ − s) = (rπ − s)^∘(rπ − s) = [deg(rπ − s)]`,

while expanding the left side by ring algebra in End(E), using `V∘π = [q]` and
`V + π = [t]`,

> `(rV − s)∘(rπ − s) = r²·(V∘π) − r·s·(V + π) + s² = r²[q] − r·s·[t] + s² = [Q(r,s)]`.

Equating, `[deg(rπ − s)] = [Q(r,s)]`, and since `[m] = [n] ⟺ m = n`, we get
`deg(rπ − s) = Q(r,s) ≥ 0`. Done, uniformly in `(r,s)`, with no case splits.

**The irreducible content is `(rπ − s)^ = rV − s` (restricted dual additivity).** Note the
sign of `t` enters through `V + π = [t]`; this is exactly why one cannot shortcut to
`deg(rπ − s) = |Q(r,s)|` (which would be useless) — the dual *identification* is what fixes
the sign and delivers `Q ≥ 0`. (This is the same point as your earlier rejection of the
Frobenius-plane short-circuit: `V + π = [t]` carries the substance, and it is not a formal
consequence of `Vπ = πV = [q]`.)

---

## 4. What is already shipped (common to all routes)

All of the following are complete and depend only on the standard axioms:

1. **Verschiebung dual existence**: `V` with `V∘π = π∘V = [q]` exists as a genuine isogeny
   (Silverman III.6.1 Case 2). This gives us `π̂ = V` concretely.
2. **Trace identity at the point-map level**: `π + V = [t]` as homomorphisms on points,
   proved unconditionally via a Lagrange/`#E·P = O` argument — *not* via the addition
   pullback. (The gap is whether this lifts to an equality of *isogenies*; see Wall B.)
3. **Degree-composition `φ̂∘φ = [deg φ]`**: content-complete, cascading on a general dual
   existence statement (the ~2000-line III.6.1 keystone, still open in general; available
   concretely for π via item 1).
4. **The π-side genuine isogeny `rπ − s`**: constructed with a real pullback. Its
   pole-order-at-infinity bound (needed for the construction to be valid) is shipped for
   the base case and reduces, for general `(r,s)` coprime to `char`, to a *tactical*
   obstacle only (a coercion/rewrite mismatch in the order arithmetic), not a mathematical
   gap.
5. **Degree multiplicativity** `deg(φ∘ψ) = deg(φ)·deg(ψ)` (tower law), and
   `[m] = [n] ⟺ m = n`.
6. **Separability of `1 − π`** and **finite-dimensionality** — both axiom-clean (the other
   two HasseWitnesses fields).

So we have V concretely, the trace identity on points, and the degree-composition law
modulo dual existence. What we do **not** have is the dual-additivity identification
`(rπ − s)^ = rV − s` at the level where degree lives (the pullback).

---

## 5. The three routes and their status

### Route 1 — Pic⁰ functoriality (your earlier recommendation)

**Idea.** Build the isomorphism `Pic⁰(E) ≅ E` and define the dual isogeny as the functorial
pullback `φ* : Pic⁰(E) → Pic⁰(E)` transported across this isomorphism. Functoriality of `*`
is additive *for free*, so `(rπ − s)^ = rV − s` is automatic, as is `φ̂∘φ = [deg φ]`.

**In place.** The divisor/Picard layer is substantially built and axiom-clean (under
`[IsAlgClosed]` and `[NeZero 2], [NeZero 3]` from the Miller pipeline): projective divisors,
degree-zero subgroup, principal divisors, the chord/tangent/vertical principal-divisor
identities (Abel–Jacobi inputs), `Pic⁰` and `Pic`. A char-2/3 generalisation pathway is
identified.

**Open.** `Pic⁰(E) ≅ E` itself (the group-isomorphism keystone) and "dual = Pic⁰ pullback"
functoriality. This is the largest of the three builds, but it produces dual additivity and
the degree-composition law in **full generality and reusably** — the only route that yields
mathlib-grade dual-isogeny infrastructure rather than a Hasse-specific computation.

### Route 2 — Abstract degree-square (we have called it "W4-A")

**Idea.** Avoid building the dual functor; instead prove the composition identity
`(rV − s)∘(rπ − s) = [Q(r,s)]` **at the isogeny level** directly, exhibit `rV − s` as the
dual by the defining property `φ̂∘φ = [deg φ]`, and conclude `deg(rπ − s) = Q(r,s)`.

**In place.** The point-map expansion `(rV − s)∘(rπ − s) = [Q(r,s)]` is easy ring algebra
from items 4.1–4.2. Degree multiplicativity and `[m]=[n]⟺m=n` are shipped.

**Open / our worry.** Lifting the point-map composition identity to an **isogeny-level**
identity (so that the degree law applies) is exactly the same pullback-from-point-map gap as
Wall B. And there is a sign subtlety we want you to confirm: the composition identity plus
degree-multiplicativity alone yields `deg(rπ − s)·deg(rV − s) = Q(r,s)²`, i.e.
`deg(rπ − s) = |Q(r,s)|` — which does **not** by itself give `Q ≥ 0`. Pinning the sign seems
to require that `rV − s` is genuinely the dual (`(rV−s)∘(rπ−s) = [deg(rπ−s)]`), i.e. full
dual identification — at which point Route 2 may be no lighter than Route 1. **Is our worry
correct, or is there a clean sign-closure we are missing?**

### Route 3 — Explicit coordinate pullback ("Walls A and B")

**Idea.** Compute the pullback of `(rV − s)∘(rπ − s)` on the coordinate functions directly,
showing it equals the `[Q(r,s)]` pullback. ~70% of the supporting machinery is built
(σ–V commutation, the addition-pullback construction, the π-side pole bound, witness-
parametric consumers ready to receive the result). But our own decomposition passes hit
three obstructions, two of them genuine:

- **Wall A (V-side pole order).** To validate the construction of `rV − s` we need the
  pole order at infinity of `(rV − s)*x`. The π-side analogue is shipped by a unique-dominant-
  term argument. On the V-side the reduced numerator has a **3-way tie** at the dominant
  order (`−6` in the relevant normalisation) among `X₁²X₂`, `X₁X₂²`, `−2Y₁Y₂`, with no
  unique dominant term, so the strict-domination argument fails. Resolving it needs either a
  curve-coefficient identity showing the three terms do not fully cancel, or the general
  ramification-at-infinity formula `ord_O(φ*x) = −2·deg_i(φ)`. This is a real obstruction,
  not tactical, and is entangled with the ordinary/supersingular distinction (`deg_i(V) = 1`
  ordinary vs `= q`-flavoured supersingular).

- **Wall B (pullback from point-map).** Even granting `(rV − s)∘(rπ − s) = [Q]` on points
  (easy), concluding the **pullback** equality is *false in general* in our setup (the
  placeholder issue of §2). It reduces to the explicit Silverman III.6.3 addition formula
  for the pulled-back coordinates, `addPullback(π, V) = [t]*` on both x and y (~200–400
  lines of curve-specific computation).

- **Char-divisible edges.** When `char | r` or `char | s` (but the integers are nonzero),
  the genuine `rπ − s` construction needs the `[p] = V∘π` factorisation handled separately.
  Our decomposition recommends that Routes 1/2 moot this entirely (uniform in `(r,s)`),
  whereas Route 3 must treat it case-by-case.

**Convergent signal.** Independent decomposition passes on Wall B, the V-side pole bound,
and the char-divisible edges *each* concluded "rejected for the explicit route — use the
abstract/dual route instead." This matches your earlier "the direct degree computation is
not a shorter route."

---

## 6. Where we're stuck — the decision

We are not stuck on a proof; we are stuck on a **route commitment**, because the three
routes share one irreducible core (dual additivity on the plane) but differ enormously in
build size, reusability, and how cleanly they handle the supersingular and char-divisible
cases. We have momentum on Route 3's machinery but have hit its genuine walls; Route 1 is
your earlier pick and the only reusable one but is the biggest build; Route 2 looks lighter
but we suspect it secretly needs Route 1's content to close the sign.

We also note a structural lemma that might cut across all three: **"a genuine isogeny is
determined by its point-map"** (equivalently, the pullback is a function of the point-map).
This is true in ordinary mathematics and would collapse Wall B and the lift step of Route 2
— it would let the shipped point-map identities (`π + V = [t]`, the composition `= [Q]`)
transfer to the isogeny/pullback level directly. It would **not** by itself close the sign
(we would still need the dual identification), but it would remove the largest computational
obstacle. We have not pursued it because the placeholder isogenies make the naive universal
statement false; restricted to genuine isogenies it should hold.

---

## 7. Questions for you

**Q1 (the main one).** Given what is now shipped — V as a concrete dual of π, the trace
identity `π + V = [t]` on point-maps, and `φ̂∘φ = [deg φ]` modulo dual existence — which
route do you recommend for the keystone `(rπ − s)^ = rV − s` on `ℤπ + ℤ`: Pic⁰
functoriality (Route 1), the abstract degree-square (Route 2), or finishing the explicit
coordinate computation (Route 3)? Has your earlier Pic⁰ recommendation changed now that V
and the point-level trace identity are in hand?

**Q2 (is there something simpler?).** Is there a path to `Q(r,s) ≥ 0` that we are not
seeing — one that avoids the full dual-additivity identification? For instance, can the
non-negativity be obtained from the parallelogram law for `deg` together with `deg ≥ 0`
without separately constructing `rV − s` as the dual; or from a `deg(rπ − s) = #ker(rπ − s)`
point-count for the separable members (as we do for `1 − π` in V.1.3); or via the Weil
pairing / a determinant identity, given what we already have?

**Q3 (the sign subtlety in Route 2).** Is our analysis in §5 Route 2 correct that the
composition identity `(rV − s)∘(rπ − s) = [Q]` plus degree-multiplicativity yields only
`deg(rπ − s) = |Q(r,s)|`, and that closing the sign requires the genuine dual
identification — so Route 2 is not actually lighter than Route 1? Or is there a clean
sign-closure (e.g. positivity of the leading coefficient `q > 0` plus a continuity/density
argument on the plane) that makes Route 2 genuinely cheaper?

**Q4 (the structural shortcut).** Is "a genuine isogeny is determined by its point-map,
hence its degree is a function of the point-map" the right lemma to invest in? If proven
(for genuine isogenies, sidestepping the placeholder artefacts), would you expect it to
collapse Wall B and the Route-2 lift step, reducing the keystone to the shipped point-map
identities plus the dual identification — and is that dual identification then the genuine
irreducible residue regardless of route?

**Q5 (supersingular).** Whichever route we pick, where is the cleanest place to absorb the
ordinary/supersingular distinction (`deg_i(V) = 1` vs supersingular)? Route 3 hits it head-on
in the V-side pole order; do Routes 1/2 genuinely avoid an explicit case split, or does it
reappear elsewhere (e.g. in dual existence for supersingular curves)?

---

## 8. Document metadata

- Project: Hasse bound for elliptic curves over finite fields (Lean 4 / mathlib).
- Build status: assembled; the bound is sorry-free downstream of the two HasseWitnesses
  leaves; V.1.3 decomposed and dispatchable; III.6.3 is this brief's subject.
- Prior context: the May round-trip (Frobenius-plane short-circuit rejected; Pic⁰
  recommended for reusable infrastructure; restricted dual additivity on `ℤ[π]` flagged as
  the ~100–200-line true bottleneck; two-variable form essential; supersingular caveat that
  `rπ − s` may vanish for nonzero `(r,s)`).
- References: Silverman, *The Arithmetic of Elliptic Curves* (GTM 106), III.4 (isogenies),
  III.6.1–6.3 (dual isogeny, degree quadratic form), V.1.1–1.3 (Hasse); Sutherland, *18.783
  Elliptic Curves*, Lecture 7 (Hasse via the quadratic form).
