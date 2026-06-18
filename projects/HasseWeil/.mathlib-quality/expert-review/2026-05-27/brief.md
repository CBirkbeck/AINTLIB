# Review brief (round 4) — Hasse bound formalization: the V.1.3 degree identity `deg(1−π) = #E(F_q)`

*Prepared 2026-05-27 for the same arithmetic-geometry reviewer as rounds 1–3. Self-contained;
no repository access required. Rounds 1–3 concerned the **other** open witness (the
quadratic-form non-negativity `qf_nonneg`). This round concerns the remaining witness, **V.1.3**,
and is a focused follow-up — not a full project brief.*

## 1. Goal and the one identity at issue

We are formalizing Hasse's theorem `|#E(F_q) − (q+1)| ≤ 2√q` for an elliptic curve `E` over a
finite field `F_q` (`q = #F_q`, `π` the `q`-power Frobenius endomorphism, `t = tr(π)`). The whole
proof is assembled and reduced to **two** remaining facts; rounds 1–3 addressed the quadratic-form
one. This brief is about the second:

> **V.1.3.** `sep-deg(1 − π) = #E(F_q)`, where `1 − π` is the (genuine, separable) isogeny
> `P ↦ P − π(P)` and `sep-deg` is the separable degree of the induced function-field extension.

Because `1 − π` is **separable** (we have proved this: the invariant-differential coefficient
`ω(1−π) = 1 ≠ 0`), its separable degree equals its full degree, and the kernel cardinality equals
the degree. So V.1.3 is equivalent to the textbook identity

> **(R)** `deg(1 − π) = #E(F_q)`  ⇔  `#ker(1 − π) = #E(F_q)`.

Mathematically (R) is elementary and standard (it is the engine of the whole point-count): the
geometric kernel `ker(1−π)(K̄) = {P̄ ∈ E(K̄) : π(P̄) = P̄}` is exactly the Frobenius-fixed locus,
which is `E(F_q)`, and `1−π` separable gives `deg = #ker(K̄)`. **Our difficulty is purely one of
formalization strategy**, and that is what we would like your guidance on.

## 2. Setting, notation, and the formalization constraint that creates the problem

- `K = F_q`, `K̄` an algebraic closure, `K(E)` the function field of `E`.
- An *isogeny* in our development carries, independently, (i) a function-field pullback
  `φ* : K(E) → K(E)` (an injective `K`-algebra map) and (ii) a group homomorphism on points; the
  **degree is defined as the field-extension degree `[K(E) : φ*K(E)]`** (a `finrank`), and the
  *separable* degree as the corresponding separable-degree of that extension.
- **Crucial constraint.** Our points are, by default, the **`K`-rational** points `E(K) = E(F_q)`.
  We have the rational statement cleanly: since `π` acts as the identity on `E(F_q)`,
  `ker(1−π)` (as a subgroup of `E(K)`) is all of `E(F_q)`, so `#(rational kernel) = #E(F_q)`. What
  we do **not** have is the **geometric** picture: the `K̄`-points `E(K̄)`, the Frobenius action on
  them, and the fact that its fixed locus is `E(F_q)`.

The gap between (R) and what we have is therefore exactly:

> `deg(1−π) = #ker(1−π)(K̄)` (geometric kernel, `= sep-deg`)  versus  `#E(F_q) = #ker(1−π)(K)`
> (rational kernel). Equivalently: **the geometric kernel has no points beyond the rational ones.**

## 3. References

- [Silverman 2009] J. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., GTM 106, Springer.
  II.2.6 (fiber sizes of separable maps; generic fiber `= deg_s`), III.4.5/4.10 (separable
  /inseparable degree; kernel cardinality), III.5.5 and V.1.1 (Frobenius, `#E(F_q) = deg(1−φ_q)`).
- [Mumford, *Abelian Varieties*] for "separable isogeny with constant kernel ⟹ the function-field
  extension is Galois with group the kernel" (the deck-transformation viewpoint), if that is the
  cleaner route.
- Lang's theorem (`1 − Frob` surjective on a connected group over `F_q`, kernel `= G(F_q)`) is the
  conceptual source of (R), if you think a Lang-type formalization is preferable.

## 4. The three routes we have explored, and where each bottoms out

All three reduce to (R); the question is which to invest in.

**Route A — function-field places over `F_q` (ramification).** Realise the kernel points as the
poles of `f = x∘(1−π)` and count them as height-one primes of the integral closure of `K[1/f]` in
`K(E)` lying over `(1/f)`. We pushed this far: the ramification index at each kernel prime is `2`
(proved, axiom-clean) and the inertia/uniformity reductions are done. **It dead-ends** at the
surjectivity "every prime over `(1/f)` is one of the kernel primes". Over a *non-closed* field this
is false for a bare prime — a prime over `(1/f)` could have residue field a proper extension of `K`
(a closed point of degree > 1, i.e. a Galois orbit of geometric points), and the no-poles-off-the-
kernel facts only *consume* a `K`-rational point, they cannot *produce* one. So Route A needs
exactly the "no geometric kernel points beyond rational" fact — i.e. (R) again — and the standard
prime↔point dictionary it would use is, in our library, available **only over an algebraically
closed base**.

**Route B — base-change to `K̄`, then descend (our current preferred route).**
1. `sep-deg(1−π) = deg(1−π)` (separable). ✔ available.
2. `deg(1−π) = deg((1−π)_{K̄})` (degree is preserved under base change; `finrank` of the
   base-changed extension). Glue available; the field-isomorphism `K(E_{K̄}) ≅ K(E) ⊗_K K̄` is the
   substance, deferred to step 3.
3. **Construct `(1−π)_{K̄}` and identify it with `1 − Frob_{K̄}`** over `E_{K̄}`. *Not yet built* —
   we have a parametric base-change constructor and the base-change of Frobenius (prime
   characteristic; the general `q = p^r` case is unfinished), but no concrete base-change of
   `1 − π`.
4. Over `K̄` (algebraically closed), a separable nonconstant map of smooth curves has a fiber of
   cardinality `= sep-deg` (Silverman II.2.6), hence `#ker((1−π)_{K̄}) = deg`. **This is proved in
   our library over an algebraically closed base** (it required the inertia-degree-one and
   ramification-index-one analysis at smooth points, which is complete over `K̄`). This is the piece
   we had feared most, and it is *done*.
5. **The descent:** `#ker((1−Frob)_{K̄})(K̄) = #E(F_q)`, i.e. the `q`-Frobenius fixed locus on
   `E(K̄)` is `E(F_q)`. *Not available.* Every Frobenius-fixed-point fact we have is rational-level
   (it holds *because* `a^q = a` on the finite field `K`). The geometric version is currently an
   **assumed hypothesis** in our integration layer, never derived.
6. `#E(F_q) = #E(F_q)` (definitional). ✔

So Route B reduces V.1.3 to exactly two pieces: **(L3)** the concrete base-change `(1−π)_{K̄} =
1 − Frob_{K̄}` with degree-equality, and **(L5, the bottleneck)** the geometric descent
`#ker((1−Frob)_{K̄}) = #E(F_q)`.

**Route C — intrinsic, via the kernel as a Galois group (no `K̄`).** Since each kernel point
`T ∈ ker(1−π)` gives a translation automorphism `τ_T : P ↦ P + T` of `E` with `(1−π)∘τ_T = 1−π`,
translation by `T` induces an automorphism of `K(E)` fixing `(1−π)*K(E)`. For a separable isogeny
with **rational (constant, étale) kernel** — which is exactly our case, `ker(1−π) = E(F_q)` rational —
the standard claim is that `K(E) / (1−π)*K(E)` is **Galois with Galois group `≅ ker(1−π)`** acting by
these translations, whence `deg(1−π) = #Gal = #ker(1−π) = #E(F_q)` *intrinsically*, with no `K̄`,
no geometric kernel, and no base change. This would sidestep both L3 and L5. We have not built the
translation pullbacks or the "Galois with group = kernel" step.

## 5. A formalization hazard we want flagged

Our current integration lemma for this witness is simultaneously hypothesised over an algebraically
closed base **and** over a curve with finitely many points — two conditions that are mutually
exclusive for `E/F_q` (`F_q` is not algebraically closed; `E(K̄)` is infinite). It is therefore only
vacuously satisfiable, and it is moreover wired to a *placeholder* version of `1−π` (one whose
recorded pullback is the identity, giving spurious degree 1), not the genuine isogeny. The honest
content — the alg-closed fiber count *descended* to the finite-field point count — is hidden inside
the never-derived geometric-fixed-points hypothesis (L5). Any correct architecture must keep the
alg-closed fiber count (over `E_{K̄}`) and the finite-field conclusion (over `E/F_q`) on opposite
sides of an explicit descent, rather than conflating them in one hypothesis set.

## 6. Questions for the reviewer

**Q1 (route choice).** Given that the alg-closed fiber count (Route B step 4) is already proved in
our library, is **base-change-to-`K̄`-then-descend** the right route to `deg(1−π) = #E(F_q)`, or is
the **intrinsic Galois/translation route C** (kernel = Galois group of `K(E)/(1−π)*K(E)`) cleaner to
formalize? We are wary that Route B's descent (L5) re-introduces a geometric `K̄`-points layer we
have so far avoided everywhere else.

**Q2 (the descent, L5).** What is the cleanest formulation — and the cleanest reference — for "the
`q`-power Frobenius fixed locus on `E(K̄)` equals `E(F_q)`"? In particular: is there an argument for
`deg(1−π) = #E(F_q)` that **avoids the geometric kernel altogether** (e.g. purely via separable
degree and the rational kernel), or is passing through `E(K̄)` essentially unavoidable for the
degree-to-cardinality step? If unavoidable, is a Lang-theorem-style formulation (`1−Frob` surjective
on `E(K̄)` with kernel `E(F_q)`) preferable to a direct fixed-point computation?

**Q3 (Route C tool).** Is "*separable isogeny with rational (constant) kernel `G` ⟹ `K(E)/φ*K(E)`
is Galois with `Gal ≅ G` acting by translation, so `deg φ = #G`*" the correct and complete tool, and
what is the cleanest citation (Silverman III.4.10(b)? Mumford?)? Are there hidden hypotheses
(perfectness of `K` — true here; tame/wild ramification — `1−π` is unramified as it is separable)
that we should be careful about? Does it deliver `deg = #ker` directly, or only after a separate
"the kernel injects into the automorphism group as the full Galois group" step?

**Q4 (architecture sanity).** Independent of the route, do you agree the integration must split the
alg-closed fiber count from the finite-field point count across an explicit descent (per §5), and
that the right top-level shape is `deg(1−π) = deg((1−π)_{K̄}) = #ker((1−π)_{K̄}) = #E(F_q)` (Route B)
or `deg(1−π) = #ker(1−π) = #E(F_q)` (Route C)? Is there any reason to revive the over-`F_q`
ramification Route A, given it bottoms out in the same geometric fact?

## 7. Document metadata

- Project: Hasse bound for `E/F_q`, Lean 4 / Mathlib.
- Round: 4 (rounds 1–3 in prior correspondence concerned `qf_nonneg`).
- Status: V.1.3 reduced to `deg(1−π) = #E(F_q)`; alg-closed separable fiber count proved; the two
  open pieces are the concrete base-change of `1−π` and the geometric Frobenius-fixed-points descent
  (or, alternatively, the intrinsic Galois/translation route).
- Build: compiles; the two open pieces are isolated, named, and otherwise the V.1.3 chain is
  axiom-clean.
