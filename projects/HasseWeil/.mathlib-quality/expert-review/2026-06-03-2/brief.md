# Review brief (round 21) — Hasse bound via the finite-level Weil pairing (Route 2A)

*Prepared 2026-06-03 for the same senior arithmetic-geometry reviewer as rounds 1–20.
Self-contained: no repository access required. This continues the numbered conversation.
Since round 20 we executed your recommendations — the surjectivity-light reformulation of
the separable scaling (your Q2) and the **geometric-realisation / compatibility bridge**
(your Q1/Q5, "build one reusable compatibility layer"). Both are built and machine-checked.
The effect is to **collapse the entire remaining problem to a single, sharply-identified
geometric fact about the genuine isogenies `1−π` and `rπ−s`**. Before we commit what looks
like a multi-week formalisation effort to that fact, we want your read on whether a cheaper
route exists. The new material is §4.4 (what round-20 delivered) and §6–§7 (the sharpened
residual and the core question).*

---

## 0. Orientation

Goal: formalise Hasse's bound `|#E(𝔽_q) − q − 1| ≤ 2√q` for `E/𝔽_q`, `q = p^r`. Per your
guidance (rounds 17–19) we use **Route 2A**: build the finite-level Weil pairing
`e_ℓ : E[ℓ]×E[ℓ] → μ_ℓ` for auxiliary primes `ℓ ≠ p`, prove the scaling
`e_ℓ(ψS,ψT)=e_ℓ(S,T)^{deg ψ}` for the Frobenius pencil `ψ ∈ {π, 1−π, rπ−s}`, read off
`det(ψ | E[ℓ]) ≡ deg ψ (mod ℓ)`, and recover the integer identity
`deg(rπ−s) = q r² − t rs + s²` by varying `ℓ`; nonnegativity of a degree then gives
`Q(r,s) := q r² − t rs + s² ≥ 0`, and Cauchy–Schwarz gives Hasse.

The pairing, the scaling, the determinant reduction, and the integer endgame are **done and
axiom-clean**. As of round 20 we have also built the compatibility-bridge you prescribed.
What remains is **one** geometric input about `1−π` and `rπ−s`, described precisely in §6.
We have twice before misjudged elementary facts as deep and once the reverse; that is exactly
why we are asking rather than charging ahead.

---

## 1. Goal

Hasse's theorem for `E/𝔽_q`: `|#E(𝔽_q) − q − 1| ≤ 2√q`. Equivalently, with
`t := q + 1 − #E(𝔽_q)`, the binary quadratic form `Q(r,s) = q r² − t rs + s²` is
nonnegative for all integers `r,s`.

---

## 2. Background, conventions, references

### 2.1 Notation
- `π : E → E` the `q`-power Frobenius; `V = π̂` its dual (Verschiebung), with `Vπ = πV = [q]`
  and `π + V = [t]`.
- `[m] : E → E` multiplication by `m`. `E[ℓ] ≅ (ℤ/ℓ)²` for `ℓ ≠ p`.
- `K = 𝔽_q`, `K̄` an algebraic closure; `K(E)` the function field of `E`.
- For an isogeny `ψ`: `deg ψ` (with separable/inseparable parts `deg_s`/`deg_i`), dual `ψ̂`
  (`ψ̂ψ = [deg ψ]`); `ψ` separable ⟺ `deg_s ψ = deg ψ` ⟺ (here) `ψ^*ω ≠ 0`.
- `e_ℓ : E[ℓ]×E[ℓ] → μ_ℓ` the Weil pairing.
- `τ_S : E → E` translation by `S`; `τ_S^* : K(E)→K(E)` its comorphism `g ↦ g∘τ_S`.
- For a function `g ∈ K(E)`, `div g` its principal divisor; `ord_P g` the order at a closed
  point `P`; `(g)_0`, `(g)_∞` zero/pole divisors. `Pic⁰(E)` the degree-0 Picard group;
  `κ : Pic⁰(E) ≅ E` the Abel–Jacobi isomorphism `[(P)−(O)] ↦ P`.

**The formalisation's notion of "isogeny" (this is the crux of §6).** In our development an
`Isogeny` is a *pair of two independent data*:
- a **comorphism** `ψ^* : K(E) → K(E)` (a field embedding fixing `K`), and
- a **point map** `ψ_* : E(K̄) → E(K̄)` (a group homomorphism),

carried as **two independent fields with no built-in compatibility**. An isogeny is
**genuine** when `ψ^*` and `ψ_*` are the comorphism and closed-point map of *one and the
same* morphism of curves. For `1−π` and `rπ−s` we *do* have both data and they *are*
genuine (see §6.1) — but the predicate linking them ("for every function `h` and place `w`,
`ord_w(ψ^* h) = ord_{ψ_*(w)} h`") is not free in our framework, and supplying it is the whole
of the remaining work.

### 2.2 References
- **[Silverman]** *The Arithmetic of Elliptic Curves*, 2nd ed., GTM 106. Used:
  **II.2.6/2.7** (finite-morphism fibre counts), **II.2.12** (separable–inseparable
  factorisation `φ = λ∘Frob^e`), **III.4.10** ((a) `#φ⁻¹(Q)=deg_s φ` for all but finitely
  many `Q`, whence surjectivity; (b) `ker φ ≅ Aut(K̄(E₁)/φ^*K̄(E₂))`; (c) separable ⟹
  unramified, `#ker φ = deg φ`), **III.5.1** (`τ_Q^*ω=ω`), **III.5.2** (`(φ+ψ)^*ω=φ^*ω+ψ^*ω`),
  **III.6.1–6.2** (dual isogeny + additivity), **III.8.1–8.6** (Weil pairing properties;
  adjoint `e(φS,T)=e(S,φ̂T)`; scaling `e(φS,φT)=e(S,T)^{deg φ}`), **V.1.1** (Hasse).
- **Prior replies in this conversation.**
  - *Round 16* — the theorem-of-the-square divisor proof of `(φ+ψ)^=φ̂+ψ̂` is char-`p`-broken
    as written (the base field stays imperfect); and the trace-relation route to `deg(rπ−s)`
    is circular (identifying `rV−s` as the dual presupposes `deg(rπ−s)`).
  - *Round 17* — pivot to finite-level Route 2: `det(ψ|E[ℓ])≡deg ψ` for all `ℓ≠p`.
  - *Round 18* — separable-factorisation rescue `β = λ∘Frob^e`: Frobenius factor by Galois,
    separable factor `λ` by the separable adjoint.
  - *Round 19* — Route 2A is the path; build `e_ℓ` as a constant ratio; realise the separable
    dual as the **Picard/divisor dual** `δ = κ∘φ^*∘κ⁻¹` (multiplicity-free, *no
    coordinate-ring comorphism*); inseparable `π` via Galois.
  - *Round 20* — **(Q2)** the separable scaling can be made surjectivity-light; phrase
    degree-multiplication with `deg φ` not `#ker φ`. **(Q1/Q5)** build a single reusable
    **geometric-realisation bridge** `GeometricRealization φ` carrying *both* `pointMap_eq`
    and `pullback_eq`, prove `surjective`/`translation-covariant`/`divisor-transport` once,
    and instantiate for `1−π`, `rπ−s`, and any separable factor; do **not** rebuild all
    isogenies geometrically. Caution: the bridge must be at the level of the comorphism, not
    merely agreement on closed points.

### 2.3 State of the art
Classical (Hasse, 1930s); only the formalisation is at issue. The Stepanov/Bombieri
elementary route is a genuinely different proof we agreed not to switch to.

---

## 3. The agreed strategy (Route 2A)

1. `E[ℓ] ≅ (ℤ/ℓ)²`; build `e_ℓ`; prove bilinear / alternating / nondegenerate / Galois.
2. **Separable scaling.** For separable `φ`: `e_ℓ(φS,φT)=e_ℓ(S,T)^{deg φ}`, via the adjoint
   `e_ℓ(φS,T)=e_ℓ(S, δT)` with `δ` the Picard/divisor dual (`δ∘φ=[deg φ]`).
3. **Frobenius factor.** `e_ℓ(πS,πT)=e_ℓ(S,T)^q` (Galois: `π` acts as `q`-power on `μ_ℓ`).
4. **Determinant–degree.** With `M = (π | E[ℓ])` over `ℤ/ℓ`: `det M ≡ q`, `det(1−M) ≡ #E`
   (so `tr M ≡ t`), `det(rM−sI) ≡ Q(r,s)`.
5. **Separable factorisation** for inseparable pencil members; vacuous for `1−π`, `rπ−s`
   with `p∤s` (already separable), so step 2 applies directly.
6. **Integer separation.** The congruences for all `ℓ≠p` force the integer identity, hence
   `Q ≥ 0`, hence Hasse.

---

## 4. What is built and machine-checked (no `sorry`; only `propext, Classical.choice,
Quot.sound`)

### 4.1 The pairing and its formal properties
- `E[ℓ] ≅ (ℤ/ℓ)²` for `ℓ ≠ p`.
- `e_ℓ(S,T) = τ_S^* g_T / g_T`, where `g_T ∈ K(E)` has `div g_T = ℓ((T)) − ℓ((O))` pulled
  back through `[ℓ]` (your round-19 constant-ratio definition). Built: **`μ_ℓ`-membership,
  bilinearity in both arguments, alternating (`e_ℓ(T,T)=1`), and nondegeneracy.**

### 4.2 The separable scaling, CoordHom-free (round-19 prescription)
**Theorem (abstract separable scaling).** *Let `φ` be a separable isogeny and `δ : E → E` a
group endomorphism with `δ∘φ = [#ker φ]`. Then `e_ℓ(φS,φT) = e_ℓ(S,T)^{deg φ}`.*

We realise `δ` as the **divisor-pushforward dual** `δ = κ∘φ^*∘κ⁻¹`, where `φ^*` acts on
`Pic⁰` by pulling back divisors. The relation `δ∘φ = [#ker φ]` is **automatic via the
σ-bridge**: for the multiplicity-free pullback `φ^*((Q)) = Σ_{φP=Q}(P)` one computes
`σ(φ^*((Q)−(O))) = Σ_{φP=Q}P − Σ_{φP=O}P = δQ`, and at `Q = O` the fibre is `ker φ`, giving
`δ(φR) = #ker φ · R` for every `R` (using `R` itself as a preimage — *no surjectivity*).

### 4.3 Determinant reduction and endgame
The additive symplectic form `log e_ℓ`, the identity `det(ρ_ℓ ψ) = ` (scaling exponent of
`ψ`), the assembled reductions `Hasse ⟸ {three per-ℓ scalings}` and
`Hasse ⟸ {det M≡q, det(1−M)≡q+1−t, det(rM−sI)≡deg(r,s)}`, and the integer-separation
endgame — all built and axiom-clean.

### 4.4 What round 20 delivered (new since the last brief)

**(Q2) The scaling is now surjectivity-free.** We observed that the scaling
`e_ℓ(φS,φT)=e_ℓ(S,T)^{deg φ}` invokes the adjoint *only at the image point* `φT`, whose
preimage is the explicit `T`. Refactoring the adjoint/σ-identity to take that explicit
preimage (rather than obtaining one from a surjectivity hypothesis) makes the abstract
scaling **carry no surjectivity hypothesis at all**. This is exactly your Q2 ("reduce
dependence on point-map surjectivity").

**(Q1/Q5) The geometric-realisation bridge is built.** Following your prescription we
introduced one reusable predicate `GeometricRealization φ` for a separable `φ` over `K̄`,
bundling the genuine-isogeny data not recoverable from the two abstract fields, and proved
the **single milestone you named**:

> **Theorem (witnesses from one realisation).** *If `φ` admits a geometric realisation, then
> `φ_*` is surjective, `φ` is translation-covariant, and `φ` satisfies divisor-transport.*

It also discharges your Caution automatically: an `Isogeny` already bundles its comorphism
and point map, so `pullback_eq`/`pointMap_eq` hold definitionally, and "genuine" is a named
predicate on the pair.

**Consolidation achieved.** Feeding the bridge into the concrete pencil leaves, the
previously-separate per-isogeny inputs **translation-covariance** and **`#ker φ = deg φ`**
are now *derived* from a single underlying datum — call it **generic-point covariance**
(notation `hgcomm` below): the statement that the comorphism `φ^*` commutes with translation
*at the generic point of `E`*. So the residual, which in round 20 was a list of four
per-isogeny facts, is now **three** facts, and two of those three are visibly the *same*
underlying compatibility seen through different lenses (see §6.2).

### 4.5 Other established inputs
- `deg(1−π) = #E(𝔽_q)` (closed; this is the fixed-point count `#ker(1−π)` for the separable
  `1−π`).
- **Separability** of `1−π` and of `rπ−s` (`p∤s`): `(rπ−s)^*ω = −s·ω ≠ 0` via III.5.2, using
  the general differential additivity `a_{α+β}=a_α+a_β` (formalised).
- `#ker φ = deg φ` for separable `φ` (general).
- **Frobenius surjectivity/bijectivity over `K̄`** (`π_*` is the closed-point map of the
  `q`-power field automorphism of `K̄`, hence bijective).

---

## 5. The shape of the residual in one paragraph

Everything above is generic or already proved. To finish, we must endow each of the two
genuine separable isogenies `1−π` and `rπ−s` (base-changed to `K̄`) with the **comorphism /
point-map compatibility** that the framework leaves as a hypothesis. Concretely, three facts
remain per isogeny, and **all three are facets of one statement: that the genuine comorphism
`φ^*` (which we *do* have, §6.1) is compatible, place-by-place, with the genuine point map
`φ_*`.** The `[ℓ]` analogue of this statement is fully proved in our development (§6.3); the
question is whether the proof technique transfers, or whether `1−π`/`rπ−s` need a new and
substantial development (§6.4), and if so whether a cheaper route exists (§7).

---

## 6. Where we are stuck — the genuine comorphism's place-compatibility

### 6.1 The comorphism of `1−π` is genuine and explicit (not a fabricated object)

A recurring worry in earlier rounds was that `1−π` and `rπ−s` admit **no comorphism on the
affine coordinate ring** `K[x,y]/(…)` — correct, because `(1−π)^* x` has poles at the affine
points of `ker(1−π) = E(𝔽_q)`, so it does not lie in the coordinate ring. **But the
function-field comorphism does exist and we have it explicitly.** Writing `1−π` as the
composite `P ↦ P + (−πP)` (a sum in the group law, where `−π` is the negated Frobenius), its
comorphism is the **group-law addition rational function**: on the generic point,
`x ↦ X_add(x, x∘π, λ_add)`, where `X_add` and the slope `λ_add` are the standard affine
addition formulas. This is a bona-fide `K̄`-embedding `K(E) → K(E)`, and the abstract isogeny
`1−π` is built with *this* comorphism in its comorphism field and `id − π_*` in its
point-map field. So there is **nothing fabricated**: the two fields are the genuine
comorphism and point map of `1−π`. What is missing is purely their *compatibility predicate*.

### 6.2 The three remaining per-isogeny facts (for `φ ∈ {1−π, rπ−s}` over `K̄`)

1. **Divisor / order transport** (`hproj`): *for every `h ∈ K(E)` and every place `w`,*
   `ord_w(φ^* h) = ord_{φ_*(w)} h`. Equivalently `div(φ^* h) = φ^*(div h)` (the
   multiplicity-free fibre pullback), so `φ^*` descends to `Pic⁰` and the dual `δ` of §4.2 is
   well-defined. **This is the deepest of the three.**
2. **Surjectivity** (`hsurj`): `φ_* : E(K̄) → E(K̄)` is onto (Silverman III.4.10(a)).
3. **Generic-point translation covariance** (`hgcomm`): `φ^*` commutes with translation at
   the generic point, i.e. `τ_S^* ∘ φ^* = φ^* ∘ τ_{φS}^*` as maps `K(E) → K(E)`. From this
   single fact our bridge already *derives* the two round-20 inputs (translation covariance of
   the constant-ratio adjoint, and `#ker φ = deg φ`).

All three are *facets of the same place-compatibility* between `φ^*` and `φ_*`: (1) is it at
the level of orders of arbitrary functions; (3) is it for the specific functions obtained by
translation; (2) follows once one knows fibres have the right size (which is what transport
gives at every place). None is *mathematically* hard in Silverman — (2) is III.4.10(a), (1)
is the separable-unramified III.4.10(c) packaged as order-preservation, (3) is III.8.2. The
difficulty is entirely that our framework does not connect the two independent fields, so each
must be proved from the *explicit comorphism* of §6.1.

### 6.3 The `[ℓ]` template — what a complete proof of (1) looks like

For the multiplication isogeny `φ = [ℓ]` we have a **complete, axiom-clean proof of order
transport (1)** over `K̄`. Its engine is the explicit **division-polynomial coordinate
formula**: `[ℓ]·P = (φ_ℓ(P)/ψ_ℓ(P)², ω_ℓ(P)/ψ_ℓ(P)³)` (the standard `ℓ`-division
polynomials), available in Mathlib's elliptic-curve library as the evaluation of the
generic-point `ℓ`-multiplication at a closed point. From that formula one shows the fibre is
unramified (`e = 1` at each preimage), reads off `ord_P([ℓ]^* h)` place-by-place, and handles
the point at infinity separately by translation-invariance of the `∞`-pole order. This took a
dedicated development of roughly the scale of a long single file (≈ 900–1000 lines), including
a "same-place" comparison lemma and a Wronskian non-vanishing argument for `e=1`.

### 6.4 Why the template does not transfer to `1−π`, `rπ−s` — the precise gap

The `[ℓ]` proof bottoms out at *"evaluate the generic-point coordinate formula at a closed
point `P` and identify it with the pointwise group-law value `[ℓ]·P`"* — a fact Mathlib
provides for `[m]` via the division polynomials. **`1−π` has no such lemma.** Its comorphism
is the group-law *addition* rational function `X_add(x, x∘π, λ_add)` (§6.1), and we would need
its analogue:

> **Missing lemma (addition-formula specialisation).** *For all but finitely many closed
> points `P`, evaluating the addition rational function `X_add(·, ·, ·)` (the comorphism of
> `1−π`) at `P` equals the `x`-coordinate of the pointwise sum `P + (−πP) = (1−π)·P`.*

In our framework the addition formula and the "generic-point action" machinery operate on the
**generic point only**; there is no general principle "evaluate the affine-addition rational
function at a specialised point = the pointwise group law", analogous to the
division-polynomial specialisation Mathlib supplies for `[m]`. Building it — for the addition
map twisted by Frobenius, with the addition-denominator non-vanishing playing the role of
`ψ_ℓ(P) ≠ 0` — appears to be a fresh development on the scale of §6.3 (≈ 1000 lines),
*per the two isogenies* (though `rπ−s` should reduce to the same machinery once `1−π` is done).

### 6.5 Two facts we have *ruled out* as shortcuts (so you needn't suggest them)

- **`hsurj` cannot be folded into `hproj`.** Order transport (1) only constrains pullbacks of
  *principal* (degree-0) divisors; it says nothing about `φ^*((Q))` for a single non-principal
  place, so the natural "`deg(φ^*(Q)) = deg φ ≠ 0` ⟹ fibre nonempty" argument has no object in
  our setup. (Our only divisor-pullback is the point-map fibre sum, whose degree formula is
  itself gated on surjectivity — circular.) We have **no comorphism-side `Σ e·f = [K(E):φ^*K(E)]`
  divisor pullback**; building one is itself new infrastructure.
- **The trace route to `hsurj` is circular.** `(1−π)(1−V) = [1 − (π+V) + q] = [#E]` would give
  surjectivity of `1−π` from surjectivity of `[#E]`, *but* it needs `π+V = [1+q−#E]`, which is
  the degree-quadratic-form expansion `deg(1−π) = 1 − ⟨1,π⟩ + q` — i.e. the dual-additivity
  content you already identified as the char-`p` wall in round 16.

So `hsurj` genuinely needs either the place-compatibility of §6.2(1) or a new comorphism-side
ramification-degree theory; it is *not* obtainable from the algebra of `π, V` alone.

### 6.6 The machinery we *have* that might enable a cheaper route

We have already built a substantial **translation-divisor-transport** layer (Silverman III.8,
items 1–4), all axiom-clean:
- `placeTranslate S` — the action of translation-by-`S` on places, and `ord_P(τ_S^* h) =
  ord_{P+S}(h)` (order transport **under translation**), including the behaviour at infinity.
- `div(τ_S^* h) = τ_S^*(div h)` at the divisor level (`projectiveDivisorOf_translate`), and the
  pairing payoff `div(τ_S^* g_T / g_T) = 0` for the `[ℓ]`-invariant `g_T`.
- The fibre-pullback `pullbackDiv` under a point map and its interaction with `placeTranslate`.

In other words, order transport under *translations* is done; order transport under `[ℓ]` is
done; what is missing is order transport under the *Frobenius-twisted addition* `1−π`.

---

## 7. The core question

We are at a clean decision point: the whole bound is reduced, axiom-clean and CoordHom-free,
to the place-compatibility of §6.2 for `1−π` and `rπ−s`, whose only known proof route (§6.3)
is a ≈1000-line addition-formula coordinate development (§6.4). **Before committing that
effort we want to know whether a materially cheaper route exists.**

> **Q1 (the main question).** Is there a route to the per-place order transport `hproj` for
> `φ = 1−π` (and `rπ−s`) that **reuses the translation-transport machinery of §6.6 plus a
> decomposition of `1−π`**, rather than re-deriving an addition-formula coordinate
> specialisation (§6.4) from scratch? For instance: writing `1−π = "add P and −πP"`, can order
> transport for `1−π` be assembled from (i) the order behaviour of the *negated Frobenius*
> `−π` (purely inseparable, totally ramified, `e = q` — does this have a clean order rule?),
> (ii) the order behaviour of the *addition morphism* `m : E×E → E` restricted along the graph
> `P ↦ (P, −πP)`, and (iii) the translation-transport we already have? Or is the
> closed-point specialisation of the addition rational function genuinely irreducible — i.e.
> is the ≈1000-line development the honest cost, with no structural shortcut?

> **Q2 (surjectivity, independently).** Given that we *have* the genuine function-field
> comorphism `φ^* : K(E) → K(E)` and the finite extension `[K(E) : φ^* K(E)] = deg φ`
> (formalised), is there a clean CoordHom-free proof of `hsurj` (III.4.10(a)) that goes
> **directly through the function-field extension** — "every place of `φ^* K(E)` extends to a
> place of `K(E)` because the extension is finite, hence every closed point has a preimage" —
> *without* first proving the full place-by-place transport `hproj`? The subtlety we keep
> hitting is the final identification "place of `K(E)` over the place of `φ^* K(E)` at `Q`
> ⟺ closed point `P` with `φ_* P = Q`", which seems to need the same compatibility. Is that
> identification avoidable, or is it the irreducible core that `hproj` also needs (so that
> `hsurj` and `hproj` should simply be proved together)?

> **Q3 (generic-point covariance).** `hgcomm` (§6.2(3)) — `φ^*` commutes with translation at
> the generic point — is the one from which our bridge already derives covariance and
> `#ker=deg`. Is it provable *cheaply* directly from the explicit addition-formula comorphism
> (§6.1) and the algebra of the group law on the generic point (no closed-point
> specialisation), or does it ultimately need the same machinery as `hproj`? If it is cheap,
> we would prioritise it and isolate `hproj`/`hsurj` as the sole deep residual.

> **Q4 (granularity).** All three facets bottom at the genuine comorphism. Would you, in a
> formalisation, **build a single "geometric morphism" object for `1−π`** — comorphism + point
> map + their place-compatibility, established once from the addition formula — and derive all
> of `hproj`/`hsurj`/`hgcomm` from it (your round-20 bridge then consumes it directly)? Or is
> per-facet proof cheaper? Put differently: is the addition-formula specialisation of §6.4
> *the* thing to build, after which everything else is bookkeeping?

> **Q5 (sanity / is the residual real).** Is there any reformulation of the **separable
> scaling** itself that avoids per-place order transport for the pencil members altogether —
> e.g. a way to get `e_ℓ(φS,φT)=e_ℓ(S,T)^{deg φ}` for `φ=1−π` using only properties of `π`
> (Galois on `μ_ℓ`) and the *already-proved* `[ℓ]`-scaling and bilinearity, without ever
> transporting divisors through `1−π`? (We suspect not — the adjoint genuinely mixes `φS`,
> `τ_{φS}`, and `φ^*`, as you noted in round 20 — but given the cost of §6.4 we want to be sure
> we are not missing a pairing-level identity that sidesteps the geometry.)

---

## 8. Summary of status

| Component | Status |
|---|---|
| `E[ℓ] ≅ (ℤ/ℓ)²`, `e_ℓ` bilinear/alternating/nondegenerate | **done, axiom-clean** |
| Abstract separable scaling `e_ℓ(φS,φT)=e_ℓ(S,T)^{deg φ}` from `δ∘φ=[#ker]` | **done; now surjectivity-free (Q2)** |
| Divisor-pushforward dual `δ=κ∘φ^*∘κ⁻¹`, `δ∘φ=[#ker]` automatic | **done** |
| Determinant reduction + integer-separation endgame | **done** |
| `deg(1−π)=#E`; separability of `1−π`, `rπ−s`; `#ker=deg` (separable) | **done** |
| Frobenius factor surjectivity over `K̄` | **done** |
| Geometric-realisation bridge (round-20 Q1/Q5 milestone) | **done; consolidates covariance + `#ker=deg` into one leaf** |
| Order transport `hproj` for `[ℓ]` | **done (the template, §6.3)** |
| Translation-divisor-transport machinery (III.8 items 1–4) | **done (§6.6)** |
| **Order transport `hproj` for `1−π`, `rπ−s`** | **OPEN — §6.4, the deep residual** |
| **Surjectivity `hsurj` for `1−π`, `rπ−s`** | **OPEN — §6.5, needs §6.2(1) or new theory** |
| **Generic-point covariance `hgcomm` for `1−π`, `rπ−s`** | **OPEN — §6.2(3)** |
| Frobenius-factor scaling `e_ℓ(πS,πT)=e_ℓ(S,T)^q` (Galois) | reduced to the same per-isogeny inputs for `π`; Galois piece in place |

Everything except the bottom block is built and machine-checked. The bottom block is one
geometric fact (place-compatibility of the genuine comorphism with the point map) seen in
three lenses, for two isogenies.

---

## 9. Document metadata
- Project: Hasse bound for `E/𝔽_q` via the finite-level Weil pairing (Route 2A), in Lean 4 /
  Mathlib.
- Brief: round 21, 2026-06-03. Continues rounds 1–20.
- Build status: compiles cleanly; the remaining work is carried as explicit hypotheses
  (`hproj`, `hsurj`, `hgcomm`) on the two pencil isogenies, not as `sorry`s in the assembled
  theorems.
- Core ask: §7 — is the ≈1000-line addition-formula coordinate development the honest cost of
  `hproj`/`hsurj`/`hgcomm` for `1−π`, `rπ−s`, or is there a cheaper route reusing the
  translation-transport machinery we already have (§6.6) and a decomposition of `1−π`?
