# Decomposition: Miyake (4.6.14) Fourier vanishing — final SMO sorry

**Date**: 2026-05-19
**Target**: `LeanModularForms/SMOObligations.lean:6833` (the single remaining `sorry` in the SMO chain)
**Helper**: `miyake_descent_l_prime_gt_one_helper` (line 6662)
**Reference**: Miyake "Modular Forms" pp. 159-162 (Lemmas 4.6.6, 4.6.7; Eqs. 4.6.12, 4.6.13, 4.6.14)

## Skeleton location

The helper exists as a `:= by sorry`-ended declaration at
`SMOObligations.lean:6833`. Sub-lemmas introduced by this decomposition are to be
added immediately before the helper as `private lemma`s with `:= by sorry`.
After Step 2.5 the project must `lake build` clean (sorries-only warnings).

## Goal (from Step 1, prose)

Given:
- `f : CuspForm (Γ₁(N)) k`, `f ∈ cuspFormCharSpace k χ`.
- `p` prime with `p ∣ N`. `χ = χ'.comp unitsMap_{N → N/p}`.
- `l' > 1` squarefree, `Coprime p l'`, every prime of `l'` divides `N`.
- `h_vanish`: `a_n(f) = 0` for `Coprime n (p·l')`.
- `g_low_cast : CuspForm (Γ₁(l'·(N/p))) k`.
- `h_delta_Fourier_vanish`: `a_n(f) = a_n(V_p(g_low_cast))` for `Coprime n l'`.
- `m : ℕ` with `Coprime m l'`.

Show:

```
a_m(slash_sum_lifted(f)) = D_lifted · a_m(g_low_cast)
```

where `D_lifted := (descendCosetCount p (l'·N) : ℂ) / p` and `slash_sum_lifted` is
the descent slash sum at level `Γ₁(l'·N) → Γ₁(l'·(N/p))`.

## Plain-English proof (Miyake p. 159-162)

**Step A — Build g (Miyake p. 157, Lemma 4.6.5).** By the iterated coprime-to-`l'`
filter, there is `g : CuspForm Γ₁(l'·N) k` in `cuspFormCharSpace k (χ.comp unitsMap)`
with `a_n(g) = a_n(f)` if `Coprime n l'` and `0` otherwise. Combined with
`h_vanish` (which forces `a_n(f) = 0` for `Coprime n p` AND `Coprime n l'`), `g` is
supported on `n` with `p ∣ n` (i.e., `g ∈ qSupportedOnDvdSubmodule p`).

**Step B — Dichotomy on g (Miyake p. 156, Theorem 4.6.4).** Apply the strong
dichotomy at level `Γ₁(l'·N)` with divisor `p`. Either:
- (B-A) `g = 0` (in which case the statement collapses; the helper's `g_low_cast`
  must then also be effectively zero in the relevant range, and the goal follows
  from `multipass_V_p_slash_descendCoset`), OR
- (B-B) There is `g_p_local : CuspForm Γ₁(l'·(N/p)) k` with
  `V_p(g_p_local) = g` pointwise. `g_p_local ∈ cuspFormCharSpace k ψ` where
  `ψ.comp unitsMap_{l'·N → l'·(N/p)} = χ.comp unitsMap_{l'·N → N}` (via
  `toUnitHom_loweredCharacter`).

We focus on case (B-B); case (B-A) is a degenerate sub-case.

**Step C — Bundle Δ' := f.restrict − V_p(g_p_local).** Both `f.restrict` (at
`Γ₁(l'·N)`) and `V_p(g_p_local)` (at `Γ₁(l'·N)` since `(l'·(N/p))·p = l'·N`) lie in
`cuspFormCharSpace k (χ.comp unitsMap_{l'·N → N})`. Their difference `Δ'` is a
CuspForm in the same character space.

**Step D — Δ' has Fourier vanishing on Coprime n l'.** Case split on `p ∣ n`:
- `p ∤ n` AND `Coprime n l'`: then `Coprime n (p·l')`, so `a_n(f) = 0` by
  `h_vanish`. And `a_n(V_p(g_p_local)) = 0` by `qExpansion_one_modularFormLevelRaise_coeff`
  (the `p ∤ n` branch). Hence `a_n(Δ') = 0`. ✓
- `p ∣ n` AND `Coprime n l'`: then `a_n(V_p(g_p_local)) = a_{n/p}(g_p_local) = a_n(V_p(g_p_local)) = a_n(g)`
  (since `V_p(g_p_local) = g`). And `a_n(g) = a_n(f)` since `Coprime n l'`. Hence
  `a_n(Δ') = a_n(f) − a_n(g) = 0`. ✓

**Step E — Apply M7-sqfree to Δ' (Miyake p. 159, Lemma 4.6.7).** Since `1 < l'`,
`l'` is squarefree, all primes of `l'` divide `l'·N`, and `Δ'` has Coprime-`l'`
Fourier vanishing, M7-sqfree gives `g_q : ℕ → CuspForm Γ₁(l'·N · l'²) k =
CuspForm Γ₁(l'³·N) k` for each `q ∈ l'.primeFactors`, in the lifted character
space, with the q-expansion identity

```
∀ n, a_n(Δ') = ∑_{q ∈ l'.primeFactors, q ∣ n} a_{n/q}(g_q).
```

**Step F — Upgrade to function identity Δ'(z) = Σ_q V_q(g_q)(z) on ℍ.** Each
`V_q(g_q)` is a ModularForm at level `Γ₁(l'³·N · q)`. The lcm of the levels
`l'³·N · q` for `q ∈ l'.primeFactors` (distinct primes dividing `l'`) is
`l'³·N · l' = l'⁴·N`. Restrict `Δ'` from `Γ₁(l'·N)` to `Γ₁(l'⁴·N)` (since
`l'·N ∣ l'⁴·N`) and each `V_q(g_q)` from `Γ₁(l'³·N · q)` to `Γ₁(l'⁴·N)`. At the
common level `Γ₁(l'⁴·N)`, both sides are bundled forms.

By Step E + V_q's qExp formula `a_n(V_q(g_q)) = [q ∣ n] · a_{n/q}(g_q)`, both
sides have the same q-expansion at period 1. By `qExpansion_eq_zero_iff` applied
to their difference, the difference is the zero form, hence equal as functions
on ℍ:

```
Δ'(z) = ∑_{q ∈ l'.primeFactors} V_q(g_q)(z)  for all z ∈ ℍ.
```

**Step G — Apply slash_sum_lifted to both sides.** By linearity of the slash
sum (`SlashAction.add_slash`, `SlashAction.neg_slash`, `Finset.sum_sub_distrib`):

```
slash_sum_at_l'N(Δ')(z) = ∑_q slash_sum_at_l'N(V_q(g_q))(z).
```

Note `slash_sum_at_l'N` is the descend slash sum at level `Γ₁(l'·N) → Γ₁(l'·(N/p))`.
For `V_q(g_q)` at level `Γ₁(l'⁴·N)` (after restriction), we can use M6(1)
(`descendCosetList_slash_sum_commute`) to identify `slash_sum_at_l'N(V_q(g_q))(z)`
with `slash_sum_at_l'⁴N(V_q(g_q))(z)` as functions on ℍ.

**Step H — Apply M6(2) per q (Miyake p. 158, Lemma 4.6.6(2)).** For each
`q ∈ l'.primeFactors`, M6(2) says (with appropriate hypotheses `Coprime p q` and
`q ∣ N/p` derived from `Coprime p l'` and the hypothesis that all primes of `l'`
divide `N` and `p ∣ N`):

```
slash_sum_at_l'⁴N(V_q(g_q at l'⁴N/q))(z) = slash_sum_at_l'⁴N/q(g_q)(q • z).
```

Here `V_q(g_q at l'⁴N/q)` is the V_q-lift; for this to equal our V_q(g_q) (at level
`Γ₁(l'⁴·N)` after restriction from `Γ₁(l'³·N · q)`), we use that V_q is a level-raising
operation that commutes with restriction (since the underlying function is the same).

**Step I — Take m-th Fourier coefficient.** For the function `z ↦ slash_sum_at_l'⁴N/q(g_q)(q • z)`,
its m-th Fourier coefficient at period 1 equals the `m/q`-th Fourier coefficient of
`slash_sum_at_l'⁴N/q(g_q)` if `q ∣ m`, and 0 otherwise. For `Coprime m l'`, no
`q ∈ l'.primeFactors` divides `m`, so each summand's contribution is 0.

**Step J — Combine.**

```
a_m(slash_sum_at_l'N(Δ')) = ∑_q a_m(slash_sum_at_l'⁴N/q(g_q)(q • _)) = ∑_q 0 = 0.
```

By linearity: `a_m(slash_sum_at_l'N(f)) = a_m(slash_sum_at_l'N(V_p(g_p_local)))`.

**Step K — Bridge V_p(g_p_local) to V_p(g_low_cast).** By
`multipass_V_p_slash_descendCoset`, `slash_sum_at_l'N(V_p(g_p_local))(z) =
D_lifted · g_p_local(z)`. So `a_m(slash_sum_at_l'N(V_p(g_p_local))) = D_lifted ·
a_m(g_p_local)`.

For Coprime m l': `a_m(g_p_local) = a_m(V_p(g_p_local) at index p·m)` (by
V_p formula and `p ∣ p·m`) = `a_{p·m}(g)` (since V_p(g_p_local) = g) = `a_{p·m}(f)`
(since g's qExp equals f's at Coprime indices, and `Coprime (p·m) l'` follows
from Coprime p l' AND Coprime m l').

By h_delta_Fourier_vanish (applied at n = p·m): `a_{p·m}(f) = a_{p·m}(V_p(g_low_cast)) =
a_m(g_low_cast)`. So `a_m(g_p_local) = a_m(g_low_cast)` for Coprime m l'.

Hence `a_m(slash_sum_at_l'N(V_p(g_p_local))) = D_lifted · a_m(g_low_cast)`.

Combining J and K: `a_m(slash_sum_at_l'N(f)) = D_lifted · a_m(g_low_cast)` for
Coprime m l'. ∎

## Lemmas (in order)

### L1 (leaf, project): `miyake_g_p_supported`

- **Lean declaration**: `SMOObligations.lean:1391`
- **Status**: ✅ Already proven in the project. Used as a black-box leaf.
- **Discharged by**: existing project code.

### L2 (leaf, project): `HeckeRing.GL2.conductor_theorem_dichotomy_cuspForm_strong`

- **Lean declaration**: `Eigenforms/ConductorTheorem.lean:2384`
- **Status**: ✅ Already proven. Returns g_p with explicit character via `loweredCharacter`.
- **Discharged by**: existing project code.

### L3 (NEW): `delta_prime_coprime_l_prime_vanishing`

Bundle `Δ' = f.restrict − V_p(g_p_local)` at level `Γ₁(l'·N)` and show its qExp
vanishes at Coprime n l'.

```lean
private lemma delta_prime_coprime_l_prime_vanishing
    {N : ℕ} [NeZero N] {k : ℤ} (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    {p : ℕ} [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    {l' : ℕ} [NeZero l'] (hl'_pos : 0 < l') (hl'_sqfree : Squarefree l')
    (hpl' : Nat.Coprime p l')
    (hl'_dvd : ∀ q ∈ l'.primeFactors, q ∈ N.primeFactors)
    (hp_not_in : p ∉ l'.primeFactors)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (p * l') →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0)
    [NeZero (l' * N)] [NeZero (l' * N / p)]
    (g : CuspForm ((Gamma1 (l' * N)).map (mapGL ℝ)) k)
    (hg_qexp : ∀ n : ℕ, (ModularFormClass.qExpansion (1 : ℝ) g).coeff n =
      if Nat.Coprime n l' then (ModularFormClass.qExpansion (1 : ℝ) f).coeff n else 0)
    (g_p_local : CuspForm ((Gamma1 (l' * N / p)).map (mapGL ℝ)) k)
    (hg_p_local_lift : (⇑(HeckeRing.GL2.modularFormLevelRaise (l' * N / p) p k
      g_p_local.toModularForm') : UpperHalfPlane → ℂ) = ⇑g) :
    ∀ n : ℕ, Nat.Coprime n l' →
      (ModularFormClass.qExpansion (1 : ℝ) ⇑f).coeff n =
      (ModularFormClass.qExpansion (1 : ℝ)
        ⇑(HeckeRing.GL2.modularFormLevelRaise (l' * N / p) p k
          g_p_local.toModularForm')).coeff n := by sorry
```

- **Source**: Miyake p. 161, the "(4.6.14) input": derivation that `f − V_p(g_p)`
  has Coprime-`l'` Fourier vanishing.
- **Source claim (verbatim, from project docstrings reflecting Miyake)**:
  > "h has Fourier coprime-to-l' vanishing (a_n(h) = 0 for Coprime n l'):
  >   • p ∤ n with Coprime n l': a_n(f) = 0 (since Coprime n (p·l') by h_vanish),
  >     and a_n(V_p(g_p_local)) = 0 (V_p definition: zero unless p ∣ n).
  >   • p ∣ n with Coprime n l': a_n(V_p(g_p_local)) = a_{n/p}(g_p_local) = a_n(g)
  >     (by V_p definition + V_p(g_p_local) = g), and a_n(g) = a_n(f) (by M3's qExp identity)."
- **Discharged by**:
  - `qExpansion_one_modularFormLevelRaise_coeff` (V_p qExp formula, project lemma).
  - `qExpansion_ext2` (function equality preserves qExp).
  - Case split + h_vanish + hg_qexp.
- **LOC estimate**: ~40 LOC (case split on `p ∣ n`, qExp manipulation).
- **Verified citations exist**:
  - `qExpansion_one_modularFormLevelRaise_coeff`: `Modularforms/QExpansionSlash.lean`,
    used at `SMOObligations.lean:6220, 7220` (project decl).
  - `qExpansion_ext2`: project lemma (used throughout `SMOObligations.lean`).

### L4 (leaf, project): `miyake_4_6_7_squarefree_decomp`

- **Lean declaration**: `SMOObligations.lean:5697`
- **Status**: ✅ Already proven. Returns `g_q : ℕ → CuspForm Γ₁(N · l²) k` decomposition.
- **Discharged by**: existing project code.

### L5 (NEW): `delta_prime_eq_sum_V_q_g_q_function_level`

Function-level identity bridging M7-sqfree's q-expansion identity to a function
identity on ℍ. Required for Step F.

```lean
private lemma delta_prime_eq_sum_V_q_g_q_function_level
    {N : ℕ} [NeZero N] {k : ℤ}
    {l' : ℕ} [NeZero l'] (hl1_gt : 1 < l') (hl'_sqfree : Squarefree l')
    [NeZero (l' * N)]
    (Δ' : CuspForm ((Gamma1 (l' * N)).map (mapGL ℝ)) k)
    (hΔ'_vanish : ∀ n : ℕ, Nat.Coprime n l' →
      (ModularFormClass.qExpansion (1 : ℝ) ⇑Δ').coeff n = 0)
    (g_q : ℕ → CuspForm ((Gamma1 (l' * N * l' ^ 2)).map (mapGL ℝ)) k)
    (hg_q_qexp : ∀ n : ℕ,
      (ModularFormClass.qExpansion (1 : ℝ) ⇑Δ').coeff n =
      ∑ q ∈ l'.primeFactors,
        if q ∣ n then (ModularFormClass.qExpansion (1 : ℝ) (g_q q)).coeff (n / q)
        else 0) :
    ∀ z : UpperHalfPlane,
      (⇑Δ' : UpperHalfPlane → ℂ) z =
      ∑ q ∈ l'.primeFactors,
        ⇑(HeckeRing.GL2.modularFormLevelRaise (l' * N * l' ^ 2) q k
          (g_q q).toModularForm') z := by sorry
```

- **Source**: Miyake p. 159, eq. (4.6.7) function-level interpretation.
- **Source claim (paraphrased from Miyake p. 159, since Miyake states the function
  identity directly)**:
  > "for `l > 1` squarefree integer and `f ∈ G_k(N, χ)` with `aₙ(f) = 0` for
  > all `n` coprime to `l`, ... `f(z) = Σ_{p ∣ l} g_p(p·z)`."
- **Discharged by**:
  - `qExpansion_eq_zero_iff` applied to `Δ' − Σ_q V_q(g_q)` at level
    `Γ₁(l'·N · l'² · l') = Γ₁(l'⁴ · N)` (common restriction level).
  - V_q's qExp formula (`qExpansion_one_modularFormLevelRaise_coeff`).
  - Restriction lemmas.
- **LOC estimate**: ~60 LOC (build common level form, compute qExps, equate, derive function identity).
- **Verified citations exist**: `qExpansion_eq_zero_iff` is used throughout the file
  (e.g., `SMOObligations.lean:6584`).

### L6 (leaf, project): `miyake_4_6_6_level_commute_delta` (M6(2))

- **Lean declaration**: `SMOObligations.lean:5246`
- **Status**: ✅ Already proven. Function-level identity:
  `slash_sum_at_lN(V_l(f at N))(z) = slash_sum_at_N(f)(l • z)`.
- **Discharged by**: existing project code.

### L7 (leaf, project): `miyake_4_6_6_level_commute` (M6(1))

- **Lean declaration**: `SMOObligations.lean:5172`
- **Status**: ✅ Already proven. Slash sum at level `Γ₁(N)` equals slash sum at level
  `Γ₁(l·N)` as functions on ℍ for χ-eigenforms f.
- **Discharged by**: existing project code.

### L8 (NEW): `slash_sum_lifted_V_q_g_q_qexp_vanishing_at_coprime_m`

For a single `q ∈ l'.primeFactors`, show the m-th Fourier coefficient of the
slash sum applied to `V_q(g_q)` vanishes for Coprime m l'.

```lean
private lemma slash_sum_lifted_V_q_g_q_qexp_vanishing_at_coprime_m
    {N : ℕ} [NeZero N] {k : ℤ}
    {p : ℕ} [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    {l' : ℕ} [NeZero l'] (hl1_gt : 1 < l') (hl'_sqfree : Squarefree l')
    (hpl' : Nat.Coprime p l')
    (hl'_dvd : ∀ q ∈ l'.primeFactors, q ∈ N.primeFactors)
    (hp_not_in : p ∉ l'.primeFactors)
    [NeZero (l' * N)] [NeZero (l' * N / p)]
    (q : ℕ) (hq_in : q ∈ l'.primeFactors)
    (g_q : CuspForm ((Gamma1 (l' * N * l' ^ 2)).map (mapGL ℝ)) k)
    (m : ℕ) (hm_cop : Nat.Coprime m l') :
    (PowerSeries.coeff m) (ModularFormClass.qExpansion (1 : ℝ)
      (fun z => ∑ v : Fin (descendCosetCount p (l' * N)),
        (⇑(HeckeRing.GL2.modularFormLevelRaise (l' * N * l' ^ 2) q k
          g_q.toModularForm') ∣[k] descendCosetList p (l' * N) hp v) z)) = 0 := by sorry
```

- **Source**: Miyake p. 162, the per-summand vanishing in (4.6.14): "no q ∣ l' divides m,
  so all summands vanish."
- **Source claim (paraphrased from project docstring at line 7117-7119)**:
  > "Take Fourier coefficient at m: a_m(slash_sum_lifted(h)) = Σ_{q|l'} [q|m] ·
  > a_{m/q}(slash_sum_deeper(h_q)). For Coprime m l', no q | l' divides m, so
  > all summands vanish ⟹ a_m(slash_sum_lifted(h)) = 0."
- **Discharged by**:
  - L6 (M6(2)): push slash sum past V_q.
  - L7 (M6(1)): bridge level Γ₁(l'·N) to Γ₁(l'·N · l'²).
  - V_q's qExp formula for `z ↦ f(qz)`: `a_m(f(q·)) = a_{m/q}(f)` if `q ∣ m` else 0.
  - For Coprime m l' and q ∈ l'.primeFactors: `q ∣ l'` so `Coprime m q.dvd → ¬ q ∣ m`,
    hence the else-0 branch.
- **LOC estimate**: ~60 LOC.

### L9 (NEW): `slash_sum_lifted_delta_prime_coprime_l_prime_vanishing`

The composite claim: `a_m(slash_sum_lifted(Δ')) = 0` for Coprime m l'.

```lean
private lemma slash_sum_lifted_delta_prime_coprime_l_prime_vanishing
    {N : ℕ} [NeZero N] {k : ℤ}
    {p : ℕ} [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    {l' : ℕ} [NeZero l'] (hl1_gt : 1 < l') (hl'_sqfree : Squarefree l')
    (hpl' : Nat.Coprime p l')
    (hl'_dvd : ∀ q ∈ l'.primeFactors, q ∈ N.primeFactors)
    (hp_not_in : p ∉ l'.primeFactors)
    [NeZero (l' * N)] [NeZero (l' * N / p)]
    (Δ' : CuspForm ((Gamma1 (l' * N)).map (mapGL ℝ)) k)
    (hΔ'_vanish : ∀ n : ℕ, Nat.Coprime n l' →
      (ModularFormClass.qExpansion (1 : ℝ) ⇑Δ').coeff n = 0)
    (m : ℕ) (hm_cop : Nat.Coprime m l') :
    (PowerSeries.coeff m) (ModularFormClass.qExpansion (1 : ℝ)
      (fun z => ∑ v : Fin (descendCosetCount p (l' * N)),
        (⇑Δ'.toModularForm' ∣[k] descendCosetList p (l' * N) hp v) z)) = 0 := by sorry
```

- **Source**: Miyake p. 161-162, the (4.6.14) Fourier vanishing applied to `h`.
- **Discharged by**:
  - L4 (M7-sqfree): get g_q decomposition.
  - L5: function identity Δ'(z) = Σ_q V_q(g_q)(z).
  - L8: per-summand vanishing.
  - Linearity of slash sum + qExp.
- **LOC estimate**: ~80 LOC.

### L10 (NEW, top-level): The helper itself

`miyake_descent_l_prime_gt_one_helper` (the existing sorry at line 6833).
After all previous lemmas are filled, this composes them via:

1. Apply L1 (M3) → get `g`.
2. Apply L2 (strong dichotomy) → get `g_p_local` and its character.
3. Bundle `Δ' = f.restrict − V_p(g_p_local)`.
4. Apply L3 to get a_n(Δ') = 0 for Coprime n l'.
5. Apply L9 to get a_m(slash_sum_lifted(Δ')) = 0 for Coprime m l'.
6. By slash sum linearity (already established as `h_Δ_slash_eq` in the existing helper):
   `a_m(slash_sum_lifted(f)) = a_m(slash_sum_lifted(V_p(g_p_local)))`.
7. `a_m(slash_sum_lifted(V_p(g_p_local))) = D_lifted · a_m(g_p_local)` by
   `multipass_V_p_slash_descendCoset`.
8. Bridge `a_m(g_p_local) = a_m(g_low_cast)` for Coprime m l' (via
   h_delta_Fourier_vanish + V_p formula + g's qExp identity).
9. Combine.

- **LOC estimate**: ~80 LOC (the assembly).
- **Discharged by**: L1-L9.

## API gaps

**None** — every leaf is either:
- An existing project lemma (L1, L2, L4, L6, L7), or
- A composition of existing project lemmas (L3, L5, L8, L9, L10) with at most
  a few mathlib lemmas (Finset arithmetic, qExp linearity).

The existing project infrastructure (M3, M4-strong, M5b, M6(1), M6(2), M7-sqfree)
fully covers the mathematical content.

## Attacks attempted

### L3 attacks

- [1] Counterexample search: `lean_loogle "¬ qExpansion _ = qExpansion _"` →
  no contradicting lemma; the case split exhausts all combinations of `p ∣ n` vs
  `Coprime n l'`.
- [2] Edge cases: `n = 0`: trivially holds (both sides are 0 since a_0 of cusp forms is 0).
  `n = p` (p ∤ l'): Coprime p l', so the hypothesis applies, and p ∣ p so we're in the
  second case; a_p(V_p(g_p_local)) = a_1(g_p_local) = a_p(g) (= a_p(f) since Coprime p l').
  Verified consistent.
- [3] Hypothesis test: `Coprime p l'` is essential (otherwise the Coprime n (p·l') step in
  case 1 fails). `hg_p_local_lift` is essential. `hg_qexp` is essential (without it we
  can't equate a_n(g) and a_n(f) at Coprime n l').
- [4] Source-drift attack: the project docstring at lines 7104-7108 spells out exactly
  this argument; the Lean statement matches.
- [5] Discharge attack: `qExpansion_one_modularFormLevelRaise_coeff` returns
  `if p ∣ n then qExp(g).coeff (n/p) else 0` — verified at `SMOObligations.lean:6220`.
- **Verdict**: SURVIVED.

### L5 attacks

- [1] Counterexample search: `lean_local_search "qExpansion_eq_zero_iff"` → exists.
  No contradicting lemma found.
- [2] Edge cases: l' = 2 (single prime): one V_q term, no overlap. Function identity is
  Δ'(z) = V_2(g_2)(z); reduces to a single V_q's qExp formula. Verified.
  l' = 6 (two primes 2, 3): Δ'(z) = V_2(g_2)(z) + V_3(g_3)(z); no overlap since
  Coprime 2 3 means at any m, only at most one of [2∣m, 3∣m] for primes — wait, both
  2∣6 and 3∣6, so they overlap at m=6. Need to check the identity holds: a_6(Δ') =
  a_3(g_2) + a_2(g_3). The qExp identity from M7-sqfree gives exactly this. ✓
- [3] Hypothesis test: `hl1_gt` (1 < l') is essential — at l'=1, l'.primeFactors = ∅,
  and the sum is empty, so the function identity says Δ' = 0 identically, which is
  trivially true if Δ' vanishes (l'=1 case is handled separately by
  `miyake_descent_l_prime_eq_one_helper`).
- [4] Source-drift attack: Miyake p. 159 states the function identity `f(z) = Σ g_p(pz)`
  for the inductive setup. The Lean statement matches.
- [5] Discharge attack: `qExpansion_eq_zero_iff` is `qExpansion 1 f = 0 ↔ f = 0`
  for f a ModularForm at level with 1 as a strict period. Verified.
- **Verdict**: SURVIVED.

### L8 attacks

- [1] Counterexample search: For Coprime m l', need q ∤ m for ALL q ∈ l'.primeFactors.
  Since each q ∣ l' and Coprime m l', we have ¬ q ∣ m (else q ∣ gcd(m, l') = 1).
  Search for a lemma `Nat.Coprime _ _ → ¬ _ ∣ _`: `Nat.Coprime.not_dvd_of_mem_primeFactors`
  or similar; exists.
- [2] Edge cases: m = 0: q ∣ 0 trivially, but Coprime 0 l' implies l' = 1, which contradicts
  hl1_gt. So m = 0 is excluded. m = 1: Coprime 1 l' always; q ∤ 1 for q > 1. ✓
- [3] Hypothesis test: All hypotheses necessary. Without Coprime p l', M6(2) can't apply.
- [4] Source-drift attack: Miyake p. 162 says exactly "no q | l' divides m, so all
  summands vanish." Lean statement matches.
- [5] Discharge attack: M6(2) (verified at SMOObligations.lean:5246). M6(1) (verified at
  SMOObligations.lean:5172). qExp formula for V_q (verified).
- **Verdict**: SURVIVED.

### L9 attacks

- [1] Counterexample search: by Step E + Step F, Δ' decomposes as Σ_q V_q(g_q). By Step I,
  each summand's m-th coefficient is 0 for Coprime m l'. By linearity, the sum is 0.
- [2] Edge cases: Δ' = 0 (degenerate): trivially holds. Δ' nontrivial: each g_q nonzero
  possibly, but per-summand vanishing at coprime m forces sum to vanish.
- [3] Hypothesis test: hl1_gt (1 < l') essential (else l'.primeFactors empty, sum trivial).
  hΔ'_vanish essential (input to M7-sqfree).
- [4] Source-drift attack: Miyake p. 161-162 says this exactly.
- [5] Discharge attack: L4 (M7-sqfree, project lemma), L5 (new), L8 (new). All in the
  decomposition tree.
- **Verdict**: SURVIVED.

### L10 (top-level helper) attacks

- [1] Counterexample search: the proof composes L1-L9; no obvious counterexample. The
  helper is called from `miyake_descent_witness_exists` which is part of the M8 chain.
- [2] Edge cases: m = 0: typically a_0 = 0 for cusp forms, trivially holds.
  l' = 2: smallest 1 < l' case, single prime; reduces to the simpler structure of L9.
- [3] Hypothesis test: All hypotheses of the helper are essential; this is captured by
  the existing helper signature.
- [4] Source-drift attack: the helper docstring (lines 6631-6661) directly cites
  Miyake p. 161-162; the Lean statement matches.
- [5] Discharge attack: relies on L1-L9. All recursively attacked.
- **Verdict**: SURVIVED.

## Prior-B2 log consultation

`.mathlib-quality/b2_log.jsonl` does not exist in this repository (no prior B2
events for this helper recorded). The previous worker's note (the user's
message context) indicates phases A, B, C.1 are proven; only the final
(4.6.14) Fourier vanishing remains. No prior B2 on the helper itself.

## Source check — Miyake quotes (verbatim from project docstrings)

The project does NOT have a Miyake PDF on hand, but the project's docstrings
carefully cite Miyake page numbers and reproduce the relevant claims. The
following are extracted from the existing docstrings as the project's
authoritative transcription of Miyake:

From `SMOObligations.lean:5665-5694` (M7-sqfree docstring):
> "For `l > 1` squarefree integer and `f ∈ G_k(N, χ)` with `aₙ(f) = 0` for
> all `n` coprime to `l`, there exist `g_p ∈ G_k(Nl², χ)` for each prime
> `p ∣ l` such that `f(z) = Σ_{p ∣ l} g_p(p·z)`.
> ...
> Miyake proof (p. 159-160): by induction on the number of prime factors of `l`."

From `SMOObligations.lean:5193-5246` (M6(2) docstring):
> "M6(2): Miyake Lemma 4.6.6 part (2) — descent commutes with `δ_l = V_l` (p. 158).
> ...
> Miyake's actual statement (p. 158): for f ∈ G_k(Γ_0(pN), χ),
>   (f | T_p^{(lN)})(z) = (f | T_p^{(N)})(l·z)
> where the LHS uses the level-`lN` slash sum applied to V_l(f), and the
> RHS is V_l applied to the level-`N` slash sum applied to f."

From `SMOObligations.lean:7113-7119` (helper docstring, the (4.6.14) argument):
> "Lift h to the deeper level via 4.6.6(2) ... for each q | l':
> slash_sum_lifted(h)(z) = Σ_{q|l'} (slash_sum_deeper(h_q))(qz).
> Take Fourier coefficient at m: a_m(slash_sum_lifted(h)) = Σ_{q|l'} [q|m] ·
> a_{m/q}(slash_sum_deeper(h_q)). For Coprime m l', no q | l' divides m, so
> all summands vanish ⟹ a_m(slash_sum_lifted(h)) = 0."

## Feasibility assessment

**Feasible**: every leaf is either an existing project lemma (L1, L2, L4, L6, L7)
or a focused composition of existing lemmas (L3, L5, L8, L9, L10). No new
mathematical content is required; only assembly. The decomposition tree mirrors
Miyake's proof structure on pp. 159-162. The total LOC estimate is ~250 LOC
across 5 new lemmas and 1 helper composition.

**Risks identified by adversarial pass**: none that block the gate. All 5
attack categories were applied to each new lemma; none surfaced a flaw.

**Confidence gate status**:
1. ✅ Every leaf discharged from existing project code or via a new composition.
2. ⏳ Pending: Lean skeleton not yet written (Step 2.5 — to do in next phase).
3. ✅ Source quotes per leaf provided (from project docstrings as authoritative
   transcription of Miyake p. 159-162).
4. ✅ Adversarial pass completed for each leaf.
5. ✅ Prior-B2 log clean (no log exists).
6. ✅ Decomposition tree mirrors Miyake's proof structure.

## Next step

Write the Lean skeleton (Phase 1e Step 2.5): introduce L3, L5, L8, L9 as
`private lemma`s with `:= by sorry` immediately before the existing helper.
Verify `lake build` passes (sorries-only). Then proceed to fill each lemma
in order.

## Skeleton update (2026-05-19, post-Step 2.5)

**Skeleton written and `lake build` passes** (3851 jobs, 4 sorry warnings, 0 errors).

**Structural change**: L5 (function-level identity `Δ' = Σ_q V_q(g_q)`) was
**inlined into L9** rather than stated as a separate lemma. Reason: stating L5
with `V_q(g_q)` in the conclusion required `[NeZero q]` for `modularFormLevelRaise`,
which the sum over `l'.primeFactors` doesn't naturally provide. L9 handles
the NeZero derivation inline via `haveI :=
⟨(Nat.prime_of_mem_primeFactors hq_in).ne_zero⟩` at each prime factor.

**Lean declarations written** (locations after edit):
- `delta_prime_coprime_l_prime_vanishing` at `SMOObligations.lean:6663` (L3, sorry)
- `slash_sum_lifted_V_q_g_q_qexp_vanishing_at_coprime_m` at `SMOObligations.lean:6693` (L8, sorry)
- `slash_sum_lifted_delta_prime_coprime_l_prime_vanishing` at `SMOObligations.lean:6714` (L9, sorry)
- `miyake_descent_l_prime_gt_one_helper` at `SMOObligations.lean:6762` (existing, sorry)

**`lake build` output**:
```
warning: SMOObligations.lean:6663: declaration uses `sorry`  (L3)
warning: SMOObligations.lean:6693: declaration uses `sorry`  (L8)
warning: SMOObligations.lean:6714: declaration uses `sorry`  (L9)
warning: SMOObligations.lean:6762: declaration uses `sorry`  (helper composition)
Build completed successfully (3851 jobs).
```

The decomposition is **discharged**: 1 unfocused sorry → 4 focused sorries,
each with a clear scope, a verbatim source quote, a Lean ↔ source match, and
a survived adversarial pass. The helper composition (4th sorry) is the
top-level assembly that calls L3, L8, L9 plus already-proven project lemmas
(L1 = `miyake_g_p_supported`, L2 = `conductor_theorem_dichotomy_cuspForm_strong`,
L4 = `miyake_4_6_7_squarefree_decomp`, L6 = `miyake_4_6_6_level_commute_delta`,
L7 = `miyake_4_6_6_level_commute`).

## Adversarial iteration 2 (2026-05-19) — flaw surfaced in L8 discharge

Re-attacking L8 (single-q vanishing) more carefully revealed a real flaw
in the discharge sketch:

### The flaw

L8's intended discharge is: apply M6(2) (`miyake_4_6_6_level_commute_delta`)
to push the slash sum past `V_q(g_q)`, then take the m-th Fourier
coefficient.

But M6(2)'s signature requires `f : ModularForm Γ₁(N_M62) k` at the
**smaller level** `N_M62`, where `N_M62 · l_M62 = lifted level`. For
the lifted level to be `l'·N` (matching our slash sum), we need
`N_M62 = l'·N/q` and `l_M62 = q`. So M6(2) wants `f` at level
`Γ₁(l'·N/q)`.

However, M7-sqfree's output `g_q` lives at level `Γ₁(l'·N · l'²) =
Γ₁(l'³·N)` — NOT at level `Γ₁(l'·N/q)`. The natural level of M7-sqfree's
internal `F_q` (per the dichotomy at line 5879) is `Γ₁((l'·N·l'²)/q) =
Γ₁(l'³·N/q)`, still not `l'·N/q`.

`Γ₁(l'³·N)` ⊆ `Γ₁(l'·N/q)` (i.e., `l'·N/q ∣ l'³·N`), so M7-sqfree's
`g_q` is invariant under **smaller** subgroup — it might NOT be
invariant under `Γ₁(l'·N/q)`. Restricting `g_q` from level `l'³·N`
to level `l'·N/q` would require strictly more invariance than M7-sqfree
provides.

Trying to bridge via M6(1) (`miyake_4_6_6_level_commute`) requires
`V_q(g_q)` to be in `modFormCharSpace` at the **smaller** level `l'·N`,
but `V_q(g_q)` is naturally at level `Γ₁(l'³·N · q)` — likely not
invariant under the larger `Γ₁(l'·N)` group.

**Conclusion**: the proposed M7-sqfree + M6(2) chain does NOT type-check
in Lean as currently stated. The level mismatch is a real flaw, not a
bookkeeping nuisance.

### Attacks attempted (iteration 2)

- [5'] Discharge attack on L8 (re-run):
  Compose M7-sqfree's `g_q` (level `l'³·N`) with M6(2) (smaller level `l'·N/q`).
  These differ by an `l'²` factor.
  Try `lean_hover_info` on `miyake_4_6_6_level_commute_delta` —
  signature confirmed: smaller level `N`, lifted `l·N`.
  Try `lean_hover_info` on `miyake_4_6_7_squarefree_decomp` —
  signature confirmed: output level `N · l²` for input level `N`.
  Composition would require `g_q : ModularForm Γ₁(l'·N/q) k`, but
  M7-sqfree produces `g_q : CuspForm Γ₁(l'³·N) k`. Type mismatch.
- **Verdict**: discharge attack SUCCEEDED — L8 as stated cannot be
  proved by the proposed sketch. The level mismatch is binding.

### What the source actually says (re-read)

Miyake's argument on pp. 161-162 (per the project's transcription):
> "h(z) = Σ_{q|l'} h_q(qz)" (4.6.7) at the function level on ℍ, AND
> "slash_sum_lifted(h)(z) = Σ_{q|l'} (slash_sum_deeper(h_q))(qz)" (4.6.6(2))
> giving slash sums at the DEEPER level (where each h_q lives).

The key insight is that Miyake's argument operates at the **deeper level**
(where `h_q` lives, namely `l'³·N`), not at the lifted level `l'·N`.
To bridge back to our level `l'·N`, we'd use M6(1) — but M6(1) requires
the function to be in a char space at the **smaller** level.

Specifically: the slash sum `T_p` at level `l'³·N → l'³·N/p` of `V_q(h_q)`
equals the slash sum `T_p` at level `l'³·N/q → l'³·N/(qp)` of `h_q`
evaluated at `q·z` (by M6(2) with smaller level `l'³·N/q`, lifted
`l'³·N`).

Then to bridge to slash sum at our level `l'·N`, we use M6(1): slash sum
at level `l'·N` equals slash sum at level `l'³·N` for forms at level
`l'·N` in the right char space.

For this to work, `V_q(h_q)` must be in a `modFormCharSpace` at level
`l'·N`. Since `V_q(h_q)` is naturally at level `Γ₁(l'³·N · q)`, this
requires either (a) a separate lemma showing `V_q(h_q)`'s function-level
identity with a form at level `l'·N`, or (b) an alternate decomposition.

### Revised plan: use inclusion-exclusion (per expert review 2026-05-16)

The expert review on 2026-05-16 (`.mathlib-quality/expert-review/2026-05-16-SMO-obligations-plan/reply.md`)
already proposed an alternative path: **inclusion-exclusion via P_q := V_q U_q**.

For each non-empty squarefree `d = ∏ T` (where `T ⊆ l'.primeFactors`),
define `f_T := (-1)^{|T|+1} (∏_{q∈T} P_q)(f)` where `P_q = V_q U_q` is
the "project onto multiples of q" operator. `f_T` is at level `Γ_1(l'·N)`
(same level — `P_q` is naturally a same-level operator after composition)
with q-expansion `a_n(f_T)` nonzero only when `d ∣ n`.

By inclusion-exclusion: if `a_n(f) = 0` for `Coprime n l'`, then
`f = Σ_{∅ ≠ T} f_T` at the q-expansion level.

Each `f_T` is `V_d`-lifted from a form at level `Γ_1(l'·N/d)`. So
M6(2) composes cleanly: `slash_sum_at_l'N(V_d(g_T at l'·N/d)) =
slash_sum_at_(l'·N/d)(g_T)(d • z)`.

Take m-th Fourier coefficient: for `Coprime m l'` and `d > 1` squarefree
divisor of `l'`, `d ∤ m`, so the coefficient is 0.

### Revised L8 / L9 statements (NEW API gap)

**API gap (NEW)**: `slash_sum_lifted_V_d_g_d_qexp_vanishing_at_coprime_m`
— for `d` a squarefree divisor of `l'` with `d > 1`, the slash sum
applied to `V_d(g_d at l'·N/d)` has 0 m-th Fourier coefficient for
`Coprime m l'`.

This is the level-clean replacement for L8. Its proof composes M6(2) +
V_d's qExp formula cleanly because both the input and output levels
match.

**Helper L_IE (NEW, more involved)**: For `Δ'` at level `l'·N` with
`Coprime n l'` Fourier vanishing, decompose `Δ'(z) = Σ_d (-1)^{|T(d)|+1}
V_d(g_d(z))` at the function level via inclusion-exclusion.

This is the level-clean replacement for L5 + L9. Its proof:
1. For each `d ∣ l'` squarefree, define `g_d` via composition of `U_q`'s
   then a dichotomy chain to V_d-preimage.
2. Verify the q-expansion inclusion-exclusion at the period-1 level.
3. Upgrade to function identity via `qExpansion_eq_zero_iff`.

### Updated feasibility assessment

**Feasibility downgraded from "clean" to "requires new API"**.

The previous decomposition's discharge chain (M7-sqfree → M6(2)) does not
compose at the type level. A genuine refactor is needed.

The cleanest path forward, per the expert review, is the
inclusion-exclusion via `P_q = V_q U_q`. This requires:
- A `V_d U_d` operator API (or per-q composition).
- An inclusion-exclusion identity at the q-exp level.
- A function-identity bridge via `qExpansion_eq_zero_iff`.
- Cleaner per-`d` M6(2) compositions.

**Estimated additional LOC**: ~500-700 LOC of new infrastructure
(P_d operator, inclusion-exclusion lemma, function-identity upgrade,
per-d M6(2) compositions, then the helper assembly).

**Recommendation**: this is substantially more work than the previous
plan suggested. The user should be informed that the (4.6.14) Fourier
vanishing requires this level of infrastructure development, OR an
alternative simpler argument needs to be found.

### Confidence gate (iteration 2)

1. ❌ Discharge chain BROKEN — L8 (and downstream L9) cannot be discharged
   via the proposed M7-sqfree + M6(2) composition.
2. ✅ Skeleton compiles (verified).
3. ✅ Source quotes per leaf.
4. ❌ Adversarial pass REJECTED L8's discharge attack (iteration 2).
5. ✅ Prior-B2 log clean.
6. ✅ Tree mirrors source structure.

**Gate status: BLOCKED on L8/L9 discharge**. Decomposition needs revision
per the expert review's inclusion-exclusion approach.

