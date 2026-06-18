# Decomposition: Formal-group ↔ isogeny bridge (Silverman IV.1.4, IV.4.3)

**Topic.** Close the substantive `sorry`s in `HasseWeil/FormalIsogenySeries.lean`
that connect the elliptic curve's *local-expansion* data (`localExpand`,
`formalIsogenySeries`, `omegaPullbackCoeff`) to the formal-group machinery:

- **BRIDGE-001** `omegaPullbackCoeff_eq_formalIsogenyLeading`
  (`FormalIsogenySeries.lean:327`, sorry at `:330`) — Silverman **IV.4.3**:
  `omegaPullbackCoeff W α = algebraMap F K(E) (coeff 1 (formalIsogenySeries W α))`.
- **BRIDGE-003** `formalIsogenySeries_add`
  (`FormalIsogenySeries.lean:434`, sorry at `:441`) — Silverman **IV.1.4**:
  if `γ = α + β` as `AddMonoidHom`s then
  `formalIsogenySeries W γ = subst ![fα, fβ] (formalGroupLaw W).toMvPowerSeries`.
- (third, related) the EDS Wronskian inductive step
  `OmegaPullbackCoeff.lean:457`, sorry at `:477` (`wronskian_Φ_ΨSq_nat`, `m ≥ 5`).

Source read OK: Silverman 2nd ed., Chapter IV pages **115–128** (book), i.e. PDF
133–146 — IV.1 (Expansion around O), IV.2 (Formal Groups), IV.3 (Groups
Associated), IV.4 (Invariant Differential), IV.5 (Formal Logarithm). All read in
full including the proofs of Prop. 1.1, Lem. 1.2, Prop. 4.2, **Cor. 4.3**,
Cor. 4.4, Prop. 5.2.

---

## ⚠ Headline finding before any leaves: most of this is ALREADY DONE elsewhere

Two independent, **sorry-free** developments already exist that make the two
BRIDGE `sorry`s *non-load-bearing for the Hasse bound*:

1. **The abstract formal-group theory is 100% sorry-free.** All 14 files in
   `HasseWeil/FormalGroup/` have **0 `sorry`** (verified by grep). In particular
   `HasseWeil/FormalGroup/InvariantDiff.lean:155`
   `FormalGroupHom.invariantDifferential_chain` is a **complete proof** of
   Silverman **IV.4.3**:
   ```
   subst f.toSeries G.normalizedDifferential.toSeries * derivative R f.toSeries
     = C (coeff 1 f.toSeries) * F.normalizedDifferential.toSeries
   ```
   for an abstract `FormalGroupHom F G` (it forwards to
   `FormalGroup.invariantDiff_chain` in `FormalGroup/Differential.lean`, also
   sorry-free). Comparing constant coefficients gives `a = coeff 1 f`
   (`InvariantDifferential.eq_smul_normalized`, also proven). **This is the exact
   abstract content of BRIDGE-001.** What is missing is *not* IV.4.3 itself but a
   bridge object identifying the curve's `omegaPullbackCoeff`/`formalIsogenySeries`
   with a `FormalGroupHom` and its `normalizedDifferential`.

2. **III.5.2 + III.5.3 are proven axiom-clean WITHOUT the formal group**, on the
   Kähler side, in `HasseWeil/RouteBInduction.lean` (0 `sorry`):
   - `omegaPullbackCoeff_addIsog_pair` (`:82`) — III.5.2 additivity
     `a_{α₁+α₂} = a_{α₁}+a_{α₂}` for the genuine sum isogeny.
   - `omegaPullbackCoeff_mulByInt_routeB` (`:226`) — III.5.3 `a_{[n]} = n`.
   These come from the 1-dim Kähler module + `kaehler_D_addPullback_x_pair_eq_smul_omega`
   (`SilvermanIV14.lean` / `Differential.lean`), **not** from `formalIsogenySeries`.

   ⇒ The downstream consumers (separability of `1−π`, `rπ−s`; the degree quadratic
   form) get their `omegaPullbackCoeff` facts from `RouteBInduction`, so closing
   the two BRIDGE `sorry`s is **not required for the Hasse bound** (MEMORY confirms
   the bound is already proven axiom-clean). The two `sorry`s remain as the
   "honest" general-α statements of IV.4.3 / IV.1.4, valuable as a clean
   formalisation but **strictly optional**.

**Direct consumers of the two bare `sorry`s** (grep): none outside
`FormalIsogenySeries.lean` itself. `omegaPullbackCoeff_add_via_bridge_of_constCoeff`
(`:670`, which calls both bare `sorry`s) has **no external consumer** — only
docstring mentions in `AdditionPullback/{Differential,SilvermanIV14}.lean`.
`GapSpines.lean` and `Verschiebung/Genuine.lean` reference BRIDGE-003 only in
docstrings; the actual code path (`addPullback_x_pair_sum_reduces_of_iv14_witness`)
takes the IV.1.4 identity as a *hypothesis* `h_iv14`.

So this ticket is: **(A)** close BRIDGE-001 by building the curve↔abstract-FG
bridge object and invoking the already-proven IV.4.3; **(B)** close BRIDGE-003 by
the local-coordinate addition-formula identity (the genuinely new geometric work).
Both can be staged so that even partial completion (the Frobenius/`[n]`/`id`
special cases, all already shipped) keeps the file building.

---

## (a) Source: correct definitions & statements (faithful, with quotes)

### IV.1 — Expansion around O (book pp. 115–120)

Change of variables `z = -x/y`, `w = -1/y`, so `x = z/w`, `y = -1/w`. The origin
`O` becomes `(z,w) = (0,0)` and `z` is a uniformizer at `O` (order-1 zero). The
Weierstrass equation becomes
> `w = z³ + a₁zw + a₂z²w + a₃w² + a₄zw² + a₆w³ = f(z,w)`. (p. 115)

**Prop. 1.1.** (p. 116) "(a) The procedure described above gives a power series
`w(z) = z³(1 + A₁z + A₂z² + ⋯) ∈ ℤ[a₁,…,a₆]⟦z⟧`. (b) `w(z)` is the unique power
series satisfying `w(z) = f(z, w(z))`."

Laurent series for `x`, `y` and the invariant differential (p. 118):
> `x(z) = z/w(z) = z⁻² − a₁z⁻¹ − a₂ − a₃z − ⋯`,
> `y(z) = −1/w(z) = −z⁻³ + a₁z⁻² + a₂z⁻¹ + a₃ + ⋯`,
> `ω(z) = dx(z)/(2y + a₁x + a₃) = (1 + a₁z + (a₁²+a₂)z² + ⋯) dz`. (p. 118)

**Formal addition law (IV.1.4-type), pp. 119–120.** For independent
indeterminates `z₁, z₂`, set `wᵢ = w(zᵢ)`, slope
> `λ(z₁,z₂) = (w₂−w₁)/(z₂−z₁) = Σ_{n≥3} A_{n−3} (z₂ⁿ−z₁ⁿ)/(z₂−z₁)`, and
> `ν = w₁ − λz₁`. The line `w = λz − ν` meets the cubic in a third root `z₃`,
> expressible as a power series `z₃(z₁,z₂) ∈ ℤ[a₁,…,a₆]⟦z₁,z₂⟧` (p. 119).

> "Letting `w₃ = λz₃ + ν`, the three points `(z₁,w₁),(z₂,w₂),(z₃,w₃)` are
> collinear on `E`, so they add to `O`… we can compute the `w`-coordinate of
> `−(x₁,y₁)−(x₂,y₂)`." Inversion: `i(z) = x(z)/(y(z)+a₁x(z)+a₃)`. The **formal
> group law** is
> `F(z₁,z₂) = i(z₃(z₁,z₂)) = z₁ + z₂ − a₁z₁z₂ − a₂(z₁²z₂+z₁z₂²) + ⋯ ∈ ℤ[a]⟦z₁,z₂⟧`.
> (p. 120)

From the group law on `E` one deduces `F` satisfies commutativity,
associativity, and the inverse identity (p. 120). **This is precisely the
identity BRIDGE-003 asserts**: pulling back the uniformizer `z = -x/y` under
`α+β` produces `F(z∘α, z∘β)` — i.e. the *function-field* element
`(α+β)*z = -addPullback_x_pair/addPullback_y_pair` has local expansion equal to
`F̂` substituted with the two summand series. (Footnote 1, p. 123: the precise
sense is `P_{F(z,z')} = P_z + P_{z'}` for distinct points, then `z'→z` by
continuity — i.e. the addition law on `E(K)` *is* `F` in the `z`-coordinate.)

### IV.2 — Formal groups (book pp. 120–122)

**Definition** (p. 121). A one-parameter commutative formal group `F` over `R` is
`F(X,Y) ∈ R⟦X,Y⟧` with (a) `F(X,Y) = X+Y + (deg ≥ 2)`, (b) associativity, (c)
commutativity, (d) unique inverse `i(T)`, (e) `F(X,0)=X`, `F(0,Y)=Y`.

**Example 2.2.3** (p. 121): "Let `E` be an elliptic curve… The *formal group
associated to* `E` is denoted `Ê`. It is defined by the power series `F(z₁,z₂)`
described in IV§1."

**Example 2.2.4 / Prop. 2.3** (pp. 121–122). `[m] : F → F` defined inductively;
`[m](T) = mT + (higher)`; **Prop. 2.3(a)**: `[m](T) = mT + ⋯`.

### IV.4 — The invariant differential (book pp. 125–126) — **the crux for BRIDGE-001**

**Definition** (p. 125). An invariant differential `ω(T) = P(T) dT` on `F/R`
satisfies `ω ∘ F(T,S) = ω(T)`, i.e. `P(F(T,S))·F_X(T,S) = P(T)`. Normalized iff
`P(0) = 1`.

**Prop. 4.2** (p. 125). "There exists a unique normalized invariant differential
on `F/R`, given by `ω = F_X(0,T)⁻¹ dT`. Every invariant differential is `a·ω`."

**Cor. 4.3 (BRIDGE-001 content)** (p. 126):
> "Let `F/R`, `G/R` be formal groups with normalized differentials `ω_F`, `ω_G`,
> and `f : F → G` a homomorphism. Then `ω_G ∘ f = f'(T) ω_F`."
> *Proof.* `ω_G ∘ f` is an invariant differential for `F`:
> `(ω_G ∘ f)(F(T,S)) = ω_G(G(f(T),f(S)))` (f hom) `= (ω_G ∘ f)(T)` (ω_G
> invariant). By IV.4.2 it is `a·ω_F` for some `a ∈ R`; **comparing coefficients
> of `T` gives `a = f'(0)`**. ∎

So if `f(T) = a₁T + O(T²)` then the leading coefficient `a₁ = f'(0)` is exactly
the scalar by which `f` pulls back the differential. **For the curve, `α*` pulls
back `ω = dx/(2y+a₁x+a₃)` to `omegaPullbackCoeff W α · ω`, and the formal hom of
`α` is `formalIsogenySeries W α`, whose `coeff 1` is `f'(0)`. BRIDGE-001 is IV.4.3
read through the curve↔Ê dictionary.**

### IV.5 — The formal logarithm (book pp. 127–128) — *not needed here*

`log_F = ∫ ω_F`, `exp_F` its inverse (char 0 / torsion-free `R`). Already
sorry-free in `FormalGroup/Logarithm.lean`. **Not on the critical path** for
either BRIDGE `sorry` (those are characteristic-free, leading-coefficient
statements). Listed only for completeness.

---

## (b) Silverman's proof skeleton (the spine to mirror)

**BRIDGE-001 = IV.4.3 spine.** (i) `α` (genuine isogeny fixing `O`) induces a
formal-group homomorphism `f_α := formalIsogenySeries W α : Ê → Ê` of the curve's
formal group `Ê`. (ii) `α*ω` on the curve corresponds, under
`localExpand`, to `ω ∘ f_α` on `Ê` (the local expansion of the invariant
differential is `Ê`'s normalized differential — IV.1's `ω(z)` expansion). (iii)
By IV.4.3, `ω ∘ f_α = f_α'(0)·ω`, and `f_α'(0) = coeff 1 f_α`. (iv) Hence
`α*ω = (coeff 1 f_α)·ω`, i.e. `omegaPullbackCoeff W α = coeff 1 (formalIsogenySeries W α)`
(in `F ⊂ K(E)` via `algebraMap`).

**BRIDGE-003 = IV.1.4 spine.** The curve's addition law in the `z = -x/y`
coordinate is *by construction* the formal group law `F̂` (pp. 119–120). For
genuine `α, β` (reducing to `O`), `(α+β)*z` reduces to `O` and its local
expansion is `F̂((α)*z, (β)*z) = F̂(f_α, f_β)`. Coefficient-by-coefficient this is
`formalIsogenySeries W (α+β) = subst ![f_α, f_β] F̂`. (Footnote 1, p. 123:
continuity / addition-formula computation.)

---

## (c) Ordered leaves

Notation: `F := base field`, `KE := K(E)`, `Ê := formalGroupLaw W`,
`f_α := formalIsogenySeries W α`, `ω := invariantDifferential W.toAffine`,
`a_α := omegaPullbackCoeff W α`. "FG" = `HasseWeil.FormalGroup` namespace.

### Track A — BRIDGE-001 via the abstract IV.4.3 (recommended)

The whole point: **do not re-prove IV.4.3**; build the bridge object and invoke
`FormalGroupHom.invariantDifferential_chain`.

> **Leaf A0 (genuinely NEW, structural).** Build a `FormalGroup F` instance for
> the curve from the bare `formalGroupLaw W : FormalGroupLaw F`.
> ```lean
> noncomputable def curveFormalGroup (W : WeierstrassCurve F) : FG.FormalGroup F where
>   toSeries := (formalGroupLaw W).toMvPowerSeries
>   lunit := …   runit := …   assoc := …   comm := …
> ```
> Discharge: `lunit`/`runit` reduce to `formalGroupLaw_coeff_left_unit` /
> `_right_unit` (`FormalGroupAssoc.lean:114,125`, PROVEN) at the `subst`-of-`X`
> level via `MvPowerSeries.subst_X`. `assoc`/`comm`: Silverman derives them from
> the group law on `E` (p. 120). In Lean the cleanest path is the **uniqueness of
> `w(z)`** (`Prop. 1.1(b)`) already encoded in `FormalGroup.lean` /
> `FormalGroupAssoc.lean`; `assoc`/`comm` of `formalGroupLaw_coeff` are
> coefficient identities of the explicit recursive series.
> Source: IV.2 Def (p. 121) + IV.1.4 (p. 120).
> **LOC ≈ 250–500.** `lunit`/`runit` ≈ 30 each; `comm` ≈ 80–150; `assoc` is the
> hard one ≈ 150–300 (Silverman gets it free from `E`; formally it is a
> 3-variable `subst` identity on the recursive `formalGroupLaw_coeff`). **RISK:
> assoc may need substantial MvPowerSeries `subst`-composition plumbing.** See
> "alternative" note below — A0 may be sidesteppable.

> **Leaf A1 (genuinely NEW).** Package `f_α` as a `FormalGroupHom (curveFormalGroup W) (curveFormalGroup W)`:
> ```lean
> noncomputable def isogFormalHom (α) (h_genuine : constantCoeff (f_α) = 0)
>     (h_add : f_α intertwines Ê) : FG.FormalGroupHom (curveFormalGroup W) (curveFormalGroup W) where
>   toSeries := f_α
>   zero_const := h_genuine
>   preserves_add := h_add   -- = BRIDGE-003 reindexed!
> ```
> Discharge: `zero_const` = `constantCoeff_formalIsogenySeries_of_orderTop_pos`
> (PROVEN, `FormalIsogenySeries.lean:99`). `preserves_add` is exactly
> **BRIDGE-003** for the special shape `(α, α)` — so A1 *depends on Track B*.
> Source: IV.2 Def of hom (p. 121).
> **LOC ≈ 40** (pure packaging once B is available).

> **Leaf A2 (genuinely NEW — the real BRIDGE-001 identity).** Identify the curve
> differential pullback with the abstract chain rule output:
> `localExpand (a_α • ω_curve) = (coeff 1 f_α) • (normalizedDifferential Ê)`, then
> transport back. Concretely:
> ```lean
> theorem localExpand_invariantDiff_eq_normalizedDifferential :
>     -- the Laurent/Kähler image of ω = dx/(2y+a₁x+a₃) is Ê.normalizedDifferential
>     … = (curveFormalGroup W).normalizedDifferential.toSeries
> ```
> and a compatibility `localExpand (α* ω) = subst f_α (ω_Ê)` (pullback of a
> differential ↔ substitution into the formal differential). Then BRIDGE-001
> follows: by `invariantDifferential_chain`, `subst f_α ω_Ê · f_α' = C(coeff 1 f_α)·ω_Ê`,
> and since `α*ω = a_α·ω`, comparing gives `a_α = coeff 1 f_α`.
> Source: IV.1 `ω(z)` expansion (p. 118) + IV.4.2/4.3 (pp. 125–126).
> **LOC ≈ 300–600.** This is the genuine analytic content: relating the Kähler
> differential `D(α*x)·(α*u)⁻¹` on `KE` to the *formal* differential
> `P(T)dT = F_X(0,T)⁻¹ dT` of `Ê` through `localExpand`. **HARDEST leaf of Track A.**
> The differential `D x ↦ dx(z)` and `ω = u⁻¹ D x ↦ ω(z) = F_X(0,z)⁻¹ dz`
> identification is real work; `FormalGroupCorrespondence.lean` (sorry-free,
> `kaehler_rank_one`, `invariantDifferential_ne_zero`) is the staging ground.

**Alternative to A0+A2 (cheaper, parallels what already ships).** BRIDGE-001 is
*already closed for every isogeny that matters* by composing existing axiom-clean
pieces, **without** `curveFormalGroup`:
- `id`: `omegaPullbackCoeff_eq_formalIsogenyLeading_id` (PROVEN, `:732`).
- `frobenius`/`−π`: `omegaPullbackCoeff_eq_formalIsogenyLeading_negFrobeniusIsog`
  (PROVEN, `SilvermanIV14.lean:377`; both sides `= 0`).
- `[n]`: `coeff_one_formalIsogenySeries_mulByInt` (`BridgeMulByInt.lean`, 0 sorry)
  + `omegaPullbackCoeff_mulByInt_routeB` (`RouteBInduction.lean:226`).
- general sums via `omegaPullbackCoeff_add_of_leading_witness` (PROVEN, `:635`).

So the **general** `omegaPullbackCoeff_eq_formalIsogenyLeading` (`:327`) can be
left as the only "wide" statement; if a fully-general proof is wanted, Track A
(A0+A1+A2) is the source-faithful route. If only the bound is wanted, this leaf
is dead weight and can be deleted or restated witness-parametrically.

### Track B — BRIDGE-003 via the local addition formula (the genuinely new geometric work)

> **Leaf B1 (PROVEN already — reuse).** Reduce the power-series equality to the
> `coeff`-ladder n=0,1,≥2 and the order facts. All shipped:
> - n=0: `formalIsogenySeries_add_coeff_zero_via_genuine` (`:543`).
> - n=1: `formalIsogenySeries_add_coeff_one_via_FGL` (`:579`) +
>   `coeff_one_subst_bivariate` (`:164`).
> - subgroup/order: `order_formalGroupLaw_subst_pos` (`:300`),
>   `orderTop_localExpand_z_sum_pos_of_iv14_identity` (`:1825`).
> Source: IV.2.2 (a) `F = X+Y+…`. **LOC 0 (exists).**

> **Leaf B2 (genuinely NEW — the IV.1.4 identity, the irreducible core).**
> The chord-tangent addition formula in `z`-coordinate, local-expanded, equals
> `F̂` substituted with the summand series:
> ```lean
> theorem localExpand_addPullback_pair_eq_subst (α₁ α₂) (h_α₁ h_α₂ : reduce to O) :
>     localExpand W (-(addPullback_x_pair α₁ α₂)/(addPullback_y_pair α₁ α₂))
>       = ofPowerSeries ℤ F (subst ![f_{α₁}, f_{α₂}] (formalGroupLaw W).toMvPowerSeries)
> ```
> This is exactly the hypothesis `h_iv14` consumed (as a *witness*) by
> `addPullback_x_pair_sum_reduces_of_iv14_witness` (`Verschiebung/Genuine.lean:1298`).
> Discharge: this is the heart of IV.1.4 (pp. 119–120). Spine:
>   (i) `addPullback_x/y_pair` are the chord-tangent `addX/addY` of the two image
>       points (mathlib `WeierstrassCurve.Affine.addX/addY/slope`; the project's
>       `addPullback_x_pair` def, `AdditionPullback.lean:608`).
>   (ii) `localExpand` is a ring hom (`LocalExpansion.lean:798`) sending `x_gen ↦
>       formalX`, `y_gen ↦ formalY`, `algebraMap a ↦ C a`, `localParam ↦ formalX/…`.
>   (iii) The slope `λ` local-expands to Silverman's slope series `Σ A_{n-3}(z₂ⁿ−z₁ⁿ)/(z₂−z₁)`;
>       the third-root `z₃` and inversion `i(z₃)` assemble into `F̂`. The match is
>       the *definition* of `formalGroupLaw_coeff` (`FormalGroup.lean:108`,
>       degree ≤ 4 explicit, degree ≥ 5 via `bcomp/binv` of the recursive series).
> Source: IV.1.4, pp. 119–120 verbatim (slope/ν/z₃/i(z₃) display).
> **LOC ≈ 600–1200.** This is the single hardest item of the whole topic. It
> requires either (a) a `localExpand ∘ subst = subst ∘ localExpand`-style
> commutation tying the function-field addition formula to the coefficient
> recursion `formalGroupLaw_coeff`, or (b) a coefficient-by-coefficient induction
> matching `localExpand(addX/addY)` against `formalGroupLaw_coeff`. **The `≤ 4`
> coefficients are explicit and checkable directly; the `≥ 5` tail is the genuine
> recursion-matching and is the irreducible difficulty.**

> **Leaf B3 (special case, mostly PROVEN — `id + (−π)` and `[k]+[1]`).** The two
> *specific* BRIDGE-003 instances the development actually used are already reduced
> to one named witness each:
> - `coeff_one_formalIsogenySeries_isogOneSub_negFrobenius_via_bridge_003`
>   (`SilvermanIV14.lean:443`) takes the `id+(−π)` IV.1.4 identity as hyp.
> - `coeff_one_formalIsogenySeries_mulByInt_via_bridge_003`
>   (`FormalIsogenySeries.lean:832`) takes the `[k]+[1]` IV.1.4 identity as hyp.
> Closing B2 for these two shapes discharges them; the `coeff 1`-only versions are
> additionally already shipped via the Wronskian/`routeB` route, so B3 is for the
> *full series* equality, not just `coeff 1`. **LOC ≈ 50 each given B2.**

### Track C — the EDS Wronskian (`OmegaPullbackCoeff.lean:477`)

> **Leaf C1 (genuinely NEW — EDS addition formula; OUT OF SCOPE / OPTIONAL).**
> `wronskian_Φ_ΨSq_nat` for `m ≥ 5`: `Φ_m'·ΨSq_m − Φ_m·ΨSq_m' = m·preΨ(2m)`. The
> docstring (`:417–456`) gives the honest verdict: the even/odd halving step
> `W(2m) = 2·complEDS₂(2m)·W(m)` is **not** a free-ring identity; it needs the
> **EDS addition formula (Ward's relation)** at general index `j`, which **mathlib
> does not provide** (only the duplication recursions `preΨ_even`/`preΨ_odd`).
> Source: Silverman Exercise III.3.7.
> **LOC ≈ 800–2000 (new mathlib-grade EDS addition-formula API).** **STATUS:
> already bypassed.** `omegaPullbackCoeff_mulByInt_routeB` (`RouteBInduction.lean`)
> proves `a_{[n]} = n` axiom-clean via the chord recursion with no Wronskian. So
> C1 is **optional** — keep it `sorry` (it is `private`, single, isolated, and not
> on the Hasse-bound path) or develop the EDS addition formula as a separate
> mathlib contribution. Recommend: **do not attempt under this ticket.**

---

## (d) Genuinely-new definitions needed (signatures)

```lean
-- A0 (Track A): the curve's formal group as a full FG.FormalGroup structure.
noncomputable def curveFormalGroup (W : WeierstrassCurve F) [W.toAffine.IsElliptic] :
    FG.FormalGroup F
  -- toSeries := (formalGroupLaw W).toMvPowerSeries; lunit/runit/assoc/comm

-- A1 (Track A): formalIsogenySeries packaged as a formal-group hom.
noncomputable def isogFormalHom (α : Isogeny W.toAffine W.toAffine)
    (h0 : PowerSeries.constantCoeff (formalIsogenySeries W α) = 0)
    (hadd : <preserves_add for f_α>) :
    FG.FormalGroupHom (curveFormalGroup W) (curveFormalGroup W)

-- A2 (Track A): localExpand of the curve differential = Ê.normalizedDifferential,
-- and pullback ↔ subst compatibility.  (statements as in Leaf A2)

-- B2 (Track B): the IV.1.4 local addition-formula identity (the h_iv14 witness).
theorem localExpand_addPullback_pair_eq_subst
    (α₁ α₂ : Isogeny W.toAffine W.toAffine)
    (h_α₁ h_α₂ : <each reduces to O>) :
    localExpand W (-(addPullback_x_pair α₁ α₂)/(addPullback_y_pair α₁ α₂))
      = HahnSeries.ofPowerSeries ℤ F
          (MvPowerSeries.subst ![formalIsogenySeries W α₁, formalIsogenySeries W α₂]
            (formalGroupLaw W).toMvPowerSeries)
```

No genuinely-new *mathlib* primitives are needed for A0/A1/B2 beyond
`MvPowerSeries.subst` lemmas (already used heavily). C1 *would* need a new EDS
addition-formula API (out of scope).

---

## (e) Dependency order & cross-topic dependence

```
A0 curveFormalGroup  ─────────────┐
                                   ├─► A1 isogFormalHom ──┐
B2 localExpand_addPullback (=IV.1.4)──► [BRIDGE-003 :441] │
                                   └──────────────────────┤
                                                          ├─► A2 ──► [BRIDGE-001 :327]
A2 needs A0 (+ A1's preserves_add = B2 specialised)        │
                                                          ▼
B1 (exists) + B3 (given B2) close the special-case series equalities
```

Order: **B2 first** (it is also `A1.preserves_add`), then **A0**, then **A1**,
then **A2** ⇒ BRIDGE-001; B2 directly ⇒ BRIDGE-003 (+ B1 coeff-ladder). C1
independent and optional.

**Cross-topic dependencies (this is one of three concurrent topics):**
- The two BRIDGE `sorry`s feed the *omegaPullbackCoeff additivity* used by the
  **separable-isogeny / Weil-pairing** topic — BUT that topic already gets it from
  `RouteBInduction` (`omegaPullbackCoeff_addIsog_pair`), so there is **no hard
  dependency**; closing these merely provides the source-faithful IV.4.3 form.
- Leaf B2 shares the `addPullback_x_pair` / `localExpand` / `ordAtInfty`
  infrastructure with the **V-side pole-bound** topic
  (`addPullback_x_pair_x_ord_neg`, `Verschiebung/Genuine.lean:1356`): B2 is
  *exactly* the `h_iv14` hypothesis that the pole bound consumes. Closing B2
  unblocks that `sorry` too. **Coordinate B2 ownership with the pole-bound topic.**
- No dependence on the third topic beyond shared `FormalGroup/` (which is frozen,
  sorry-free, and only consumed read-only here).

---

## (f) Honest risks / hardest parts

1. **Leaf B2 (the IV.1.4 identity) is the irreducible hard core**, ≈ 600–1200 LOC.
   The `≤ 4` coefficients of `formalGroupLaw_coeff` are explicit (and the
   project's existing `SilvermanIV14.lean` already computes many `localExpand`
   leading terms — sub-helpers 1–14+), so the *low-degree* match is tractable; the
   `≥ 5` tail (recursive `bcomp/binv/formalInverse_coeff`) matching
   `localExpand(addX/addY)` is the genuine difficulty. There may be NO clean
   `localExpand ∘ subst = subst ∘ localExpand` mathlib lemma — likely need to
   prove a bespoke commutation, or do the coefficient induction by hand against
   the `w(z)` recursion `Prop. 1.1(b)`.
2. **Leaf A0 `assoc`** is "free from `E`" in Silverman but a real 3-variable
   `MvPowerSeries.subst` identity formally. May need `FormalGroupAssoc.lean`'s
   `formalGroupEval`/associativity scaffolding to be lifted to the `subst`
   formulation. ≈ 150–300 LOC, with synthesis/`whnf`-timeout risk on the curve-
   indexed `MvPowerSeries (Fin 3)` substitutions (a known pain point per MEMORY).
   **Mitigation:** A0 is *avoidable* — BRIDGE-001 for all curve-relevant isogenies
   already ships via the alternative composition (id/frob/[n]/sums). If only the
   bound matters, skip A0/A2 entirely.
3. **Leaf A2** mixes two differential formalisms (Kähler `Ω_{K(E)/F}` vs formal
   `P(T)dT`), bridged by `localExpand`. The identification
   `localExpand(ω_curve) = ω_Ê` is plausible but unproven anywhere; risk that the
   normalization constants (`F_X(0,T)⁻¹` vs `u⁻¹ D x`) require careful tracking of
   the `dz` vs `D x` conventions. ≈ 300–600 LOC.
4. **Leaf C1 (EDS Wronskian) genuinely needs new mathlib API** (Ward addition
   formula). Correctly **out of scope** — already bypassed by `routeB`. Attempting
   it here would be a multi-week mathlib contribution with no payoff for the bound.
5. **Scope honesty:** *None of these `sorry`s block the Hasse bound* (already
   proven axiom-clean per MEMORY). This ticket is "complete the source-faithful
   IV.1.4/IV.4.3 formalisation". A defensible minimal close is: **restate the two
   general `sorry`s witness-parametrically** (they already have witness wrappers)
   and **delete the bare general `sorry`s**, OR commit to Track B (B2) which is the
   one piece with genuine downstream value (the V-side pole bound).
6. **Lean pitfalls (from MEMORY + file inspection):** `abel` not `ring` for
   `FunctionField` subtraction; `RingEquiv.cast`/`exact`-not-`rw` for curve-indexed
   transports to dodge `whnf` timeouts; `set ... with` opacity breaking `rw` on
   `localExpand` let-bindings; `MvPowerSeries.subst` needs `HasSubst`
   (`hasSubst_of_constantCoeff_zero`) discharged at every site.

---

### Existing infrastructure inventory (file:decl — status)

PROVEN (sorry-free), reusable:
- `FormalGroup/InvariantDiff.lean:155` `FormalGroupHom.invariantDifferential_chain` — **IV.4.3 abstract** ✔
- `FormalGroup/InvariantDiff.lean:112` `FormalGroup.normalizedDifferential` (+ `_isNormalized`, `_unique`, `eq_smul_normalized`) ✔
- `FormalGroup/Differential.lean:47,116` `dX_at_zero`, `invariantDiff` (+ unit/mul lemmas) ✔
- `FormalGroup/Hom.lean:59,172` `FormalGroupHom.id`, `.comp` (+ `coeff_one_id`, `coeff_one_comp`) ✔
- `FormalGroup/Definition.lean:65,121` `FormalGroup`, `FormalGroupHom` structures (+ additive/mult examples) ✔
- `FormalGroupAssoc.lean:114,125` `formalGroupLaw_coeff_right_unit`, `_left_unit` ✔ (for A0 lunit/runit)
- `FormalGroup.lean:108,134` `formalGroupLaw_coeff`, `formalGroupLaw` (the bare `FormalGroupLaw`) ✔
- `RouteBInduction.lean:82,226` `omegaPullbackCoeff_addIsog_pair` (III.5.2), `_mulByInt_routeB` (III.5.3) ✔ — **the bound's actual route**
- `OmegaPullbackCoeff.lean:75,86,108` `omegaPullbackCoeff`, `_spec`, `_unique` ✔
- `FormalGroupCorrespondence.lean` `kaehler_rank_one`, `invariantDifferential_ne_zero` ✔ (staging for A2)
- `LocalExpansion.lean:798,802,811,816,855` `localExpand` (ring hom) + `x_gen↦formalX`, `y_gen↦formalY`, `algebraMap↦C`, `localParam` ✔
- `FormalIsogenySeries.lean` — the entire witness-parametric scaffold: `coeff_one_subst_bivariate` (:164), `order_formalGroupLaw_subst_pos` (:300), `formalGroupLaw_coeff_single_{zero_one,one_one}` (:127,134), `constantCoeff_formalGroupLaw` (:141), all `_of_witness`/`_via_bridge_003` closers, `formalIsogenySeries_id` (:698), `orderTop_localExpand_z_sum_pos_of_iv14_identity` (:1825), R5b `orderTop_localExpand_eq_ordAtInfty` (:1643) ✔
- `SilvermanIV14.lean` — `localExpand` leading-term sub-helpers 1–89b (many), `omegaPullbackCoeff_eq_formalIsogenyLeading_negFrobeniusIsog` (:377), `coeff_one_formalIsogenySeries_negFrobeniusIsog_eq_zero` (:359) ✔
- `BridgeMulByInt.lean` (0 sorry) `coeff_one_formalIsogenySeries_mulByInt` (BRIDGE-001 for `[n]` via Wronskian) ✔
- `Verschiebung/Genuine.lean:1298` `addPullback_x_pair_sum_reduces_of_iv14_witness` ✔ (consumes B2's `h_iv14`)

STUB (`sorry`) — the targets:
- `FormalIsogenySeries.lean:330` `omegaPullbackCoeff_eq_formalIsogenyLeading` (BRIDGE-001 general) — Track A
- `FormalIsogenySeries.lean:441` `formalIsogenySeries_add` (BRIDGE-003 general) — Track B
- `OmegaPullbackCoeff.lean:477` `wronskian_Φ_ΨSq_nat` (m≥5) — Track C (optional, bypassed)
- (adjacent, fed by B2) `Verschiebung/Genuine.lean:1356` `addPullback_x_pair_x_ord_neg` (V-side pole bound)

AXIOMATIZED / witness-carried (not a `sorry`, but a hypothesis to supply): the
`_of_witness` / `_via_bridge_003` / `addPullback_x_pair_sum_reduces_of_iv14_witness`
family — these carry the IV.1.4 identity as `h_iv14`/`h_add`, discharged by B2.
