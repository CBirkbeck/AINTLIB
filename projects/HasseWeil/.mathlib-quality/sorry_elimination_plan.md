# Sorry Elimination Plan — One by One

Total: ~28 sorry statements across 7 files + MulByIntPullback.
Strategy: attack in dependency order, grouping related sorries.

---

## Phase 0: Structural simplification (eliminates ~6 sorries instantly)

### 0a. Remove `pullback_injective` from the Isogeny structure

**Why:** An AlgHom between fields is AUTOMATICALLY injective (kernel is an ideal of a
field, hence trivial). The function field is a field (FractionRing of a domain). So
`pullback_injective` is always derivable from `pullback`.

**How:** 
1. Remove `pullback_injective` from `structure Isogeny` in Basic.lean
2. Add a derived lemma:
   ```lean
   theorem Isogeny.pullback_injective (φ : Isogeny W₁ W₂) :
       Function.Injective φ.pullback :=
     φ.pullback.injective  -- AlgHom from a field is injective
   ```
   Use: `RingHom.injective` or `Ideal.eq_bot_or_top` + `ker_eq_bot`.
3. Update ALL constructor call sites (remove `pullback_injective := ...`)
4. Update all uses of `.pullback_injective` to call the derived lemma

**Eliminates:** 6 sorry lines (Basic:175, Endomorphism:50,70, Frobenius:62, MulByIntPullback:98)
plus 2 sorries in DualIsogeny:63-64 constructor args.

---

## Phase 1: Frobenius pullback (eliminates 3 sorries)

### 1a. Fill `frobeniusIsog.pullback` (Frobenius.lean:61)

**The problem:** The Frobenius over `(W.baseChange L).toAffine` needs an L-algebra hom
on the function field. But `frobeniusAlgHom K L` is K-linear, not L-linear.

**Solution A (simple):** The Frobenius `f ↦ f^q` IS L-linear when restricted to
`(W.baseChange L).toAffine.FunctionField` because the function field of the
base-changed curve is an L-algebra, and `f^q` for `f ∈ L(E)` respects L-multiplication
(since `(cf)^q = c^q f^q = c f^q` when `c ∈ F_q ⊂ L` has `c^q = c`).

Wait — this only works for `c ∈ K` (where `c^q = c`), not general `c ∈ L`.
The Frobenius is NOT L-linear in general!

**Solution B (restructure):** Change `frobeniusIsog` to be an isogeny over K
(not over the base change to L). The pullback is on K(E), over K.
Then use `FrobeniusIsogeny.lean`'s existing sorry-free construction directly.

**How:** Replace `frobeniusIsog` definition to import from `FrobeniusIsogeny.lean`,
adding `toAddMonoidHom` as needed. The degree proof is already in
`frobeniusIsogeny_degree` (sorry-free).

**Eliminates:** Frobenius.lean:61 (pullback), :71 (degree).

### 1b. Fill `frobeniusIsog_degree` (Frobenius.lean:71)

**Already proved:** `FrobeniusIsogeny.frobeniusIsogeny_degree` in `FrobeniusIsogeny.lean`.
Just needs type-bridging.

### 1c. Fill `pointCount_eq` (Frobenius.lean:109)

**After 1a-1b:** With concrete degree, `pointCount_eq` becomes:
`pointCount = q + 1 - (1 + q - deg(1-π))`. If `deg(1-π)` is computed (not free),
this is NOT tautological — it requires `deg(1-π) = pointCount`.
This is the deep fact: `#E(F_q) = deg_s(1-π) = deg(1-π)` (separable degree).

**Approach:** Use separability of `1-π` (from `(1-π)*ω = ω ≠ 0`, proved via
invariant differential) and `#ker(1-π) = deg_s(1-π) = deg(1-π)`.

---

## Phase 2: mulByInt pullback (eliminates 2-3 sorries)

### 2a. Fill `mulByInt.pullback` (Basic.lean:172)

**How:** Wire MulByIntPullback.lean's construction into Basic.lean.
The type mismatch (WeierstrassCurve vs Affine) needs resolving:
`W.toAffine` gives an `Affine F` from a `WeierstrassCurve F`.

Key sub-task: prove `mulByInt_weierstrass` (MulByIntPullback.lean:81).

**Approach for mulByInt_weierstrass:** Specialize `zsmul_eq_smulEval` to the
generic point of K(E). The generic point `(x̄, ȳ)` is nonsingular because
`polynomialY(x̄, ȳ) ≠ 0` (from `denom_ne_zero`). Then the Jacobian point
`[n](x̄, ȳ)` lies on the curve, giving the Weierstrass identity.

### 2b. Fill `mulByInt_degree` (Basic.lean:196)

**How:** After pullback is constructed, prove `Module.finrank = n²` using:
1. `natDegree_Φ n = n.natAbs^2` (mathlib)
2. `isCoprime_Φ_ΨSq` (DivisionPolynomial.lean — proved!)
3. Extension degree of rational function = max(deg num, deg denom)
4. Tower law argument

---

## Phase 3: Endomorphism pullbacks (eliminates 2 sorries)

### 3a. Fill `isogOneSub.pullback` (Endomorphism.lean:49)

**The operation:** `(1-α)*(f) = f((1-α)(x,y))` where `(1-α)(P) = P - α(P)`.

**How:** Given `α.pullback : K(E) →ₐ[F] K(E)`, construct the pullback of `id - α`
using the **Weierstrass addition formula** on the function field:
- `(1-α)*(x) = x₃` where `x₃ = λ² + a₁λ - a₂ - x - α*(x)`,
  `λ = (y - α*(y))/(x - α*(x))`
- This is a rational function of `x, y, α*(x), α*(y)`

**Key dependency:** α.pullback must be concrete (not sorry'd).

### 3b. Fill `isogSmulSub.pullback` (Endomorphism.lean:69)

**How:** Composition of `[r] ∘ α` and `[-s] ∘ id`, then addition via the
Weierstrass formula. Builds on isogOneSub and mulByInt pullbacks.

---

## Phase 4: PullbackCoeff (eliminates 4 sorries)

### 4a. Define `isogPullbackCoeff` (PullbackCoeff.lean:79)

**How:** Given `α : Isogeny W.toAffine W.toAffine` with pullback `α*`,
define `a_α` as the unique scalar such that `D(α*(x)) = a_α · D(x)` in
Ω[K(E)/F], where D is the universal derivation.

Since Ω is 1-dimensional (kaehler_rank_one — proved!), extract the scalar using
`finrank_eq_one_iff'` and the invariant differential basis.

### 4b. Prove `a_{[n]} = n` (PullbackCoeff.lean:92)

**How:** `D([n]*(x)) = D(Φ_n/ΨSq_n)`. By the quotient rule and chain rule,
this equals `n · D(x)`. Uses the derivative of the division polynomial
rational function. Alternatively, use the formal group result
`pullbackCoeff_mulByInt` from FormalGroupAssoc.lean.

### 4c. Prove additivity and multiplicativity (PullbackCoeff.lean:108,118)

**How:** Multiplicativity (`a_{α∘β} = a_α · a_β`): chain rule on derivations.
`D((α∘β)*(x)) = D(β*(α*(x))) = a_β · D(α*(x)) = a_β · a_α · D(x)`.

Additivity (`a_{α+β} = a_α + a_β`): requires the formal group addition
formula. `(α+β)*(x)` is computed from `α*(x), α*(y), β*(x), β*(y)` via
the Weierstrass addition formula. Differentiating gives the linear term.

---

## Phase 5: Dual Isogeny (eliminates 8-10 sorries)

### Strategy: Define dual via pullback coefficient

For separable α (with `a_α ≠ 0`):
- `a_{α̂} = deg(α) / a_α` (from `α̂ ∘ α = [deg α]` and multiplicativity)
- Construct `α̂` as the endomorphism with pullback coefficient `deg(α)/a_α`

For inseparable α: `a_α = 0`, so `a_{α̂} · 0 = deg(α)` which is impossible
unless `deg(α) = 0` (i.e., α = 0). Handle separately.

**Alternative strategy:** Construct dual for [n] and Frobenius only:
- `[n]^ = [n]` (self-dual for scalars)
- `π^ = V` (Verschiebung) constructed explicitly

### 5a. `isogDual` definition (DualIsogeny.lean:33)
Define via pullback coefficient inversion for separable endomorphisms.

### 5b. `isogDual_comp_self` (DualIsogeny.lean:37)
From definition + multiplicativity of pullback coefficient.

### 5c-5g. Remaining dual properties
Each follows algebraically from 5a-5b + pullback coefficient ring hom.

---

## Phase 6: Degree quadratic form (eliminates 1 sorry)

### 6a. `degree_quadratic` (DegreeQuadraticForm.lean:88)

**With computed degrees:** `deg(rα - s)` is computed from the pullback of
`rα - s` via Module.finrank. The quadratic form identity follows from
the algebra of the function field extension.

**Alternative approach:** Use the dual isogeny + `quadratic_expansion`
(already proved as a pointwise lemma). The step from pointwise to
degree requires showing `[n]·P = [m]·P for all P ⟹ n = m`, which
needs a point of infinite order (available over the algebraic closure).

---

## Phase 7: Ramification (eliminates 2 sorries, independent)

### 7a. Integral closure (Ramification.lean:338)
Prove every element of the coordinate ring is integral over F[X].
Uses: the Weierstrass equation Y² + ... = X³ + ... gives Y as a root
of a monic polynomial over F[X].

### 7b. Separability of K(E)/F(X) (Ramification.lean:401)
Prove: the minimal polynomial of Y over F(X) is separable.
Uses: `polynomialY_ne_zero` (the derivative w.r.t. Y is nonzero).

---

## Execution Order & Parallelism

21 sorries remain. Phases marked ∥ can run in parallel.

```
DONE  Phase 0: Remove pullback_injective              [-7 sorries → 21 remain]
      │
      ├─ Phase 1a+b: Frobenius pullback+degree         [-2 sorries]  ──┐
      │                                                                │
      ├─ Phase 2a: mulByInt pullback                    [-1 sorry]     │ ∥ all three
      │                                                                │   independent
      ├─ Phase 7: Ramification                          [-2 sorries]  ─┘
      │
      ▼ (needs 1a+b done)
      Phase 2b: mulByInt degree (needs 2a)              [-1 sorry]
      │
      ├─ Phase 3: Endomorphism pullbacks (needs 2a)     [-2 sorries]  ──┐
      │                                                                 │ ∥
      ├─ Phase 4a: isogPullbackCoeff def (needs 2a)     [-1 sorry]    ─┘
      │
      ▼ (needs 3 + 4a)
      Phase 4b-c: pullbackCoeff properties              [-3 sorries]
      │
      ▼ (needs 4b-c)
      Phase 5: Dual Isogeny                             [-8 sorries]
      │
      ▼ (needs 5)
      Phase 6: degree_quadratic                         [-1 sorry]
      │
      ▼ (needs 1 + 6)
      Phase 1c: pointCount_eq                           [-1 sorry]
      │
      ▼
      DONE — 0 sorries
```

### Parallel groups:
- **Group A** (independent, start NOW): Phase 1a+b, Phase 2a, Phase 7
- **Group B** (after Group A): Phase 2b, Phase 3, Phase 4a
- **Group C** (after Group B): Phase 4b-c
- **Group D** (after Group C): Phase 5
- **Group E** (after Group D): Phase 6, then Phase 1c

Target: 0 sorries, 0 additional axioms.
