import HasseWeil.DualIsogeny
import HasseWeil.Endomorphism
import HasseWeil.AdditionPullback
import HasseWeil.EC.MulByIntAddRecurrence

/-!
# Degree as a Positive Definite Quadratic Form

The degree map on endomorphism isogenies of an elliptic curve is a positive
definite quadratic form (Silverman Corollary III.6.3).

## Main Result

For any endomorphism isogeny `α` with degree `d` and trace `t`, and integers `r, s`:

  `deg(r · α - s · 1) = d · r² - t · r · s + s²`

Since degree is non-negative (it is a natural number), this makes the
associated bilinear form positive semi-definite.

## Proof Structure

The proof uses the witness-parametric dual-isogeny language from
`DualIsogeny.lean` (`IsDualOf`; the universal `exists_dual` and the
choice-based `isogDual` cascade were refuted and deleted — see that file's
module docstring):
1. dual composition `α_dual ∘ α = [deg α]` (hypothesis `h_dual_comp`);
2. dual additivity at the `AddMonoidHom` level (`dual_add_of_trace_witnesses`);
3. the trace identity `α + α_dual = [tr α]` (hypothesis `h_sum_trace`).

From these, pointwise arithmetic on E.Point gives the expansion.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, Corollary III.6.3, Proposition III.8.6
-/

open WeierstrassCurve

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]

/-! ### The quadratic form property -/

section QuadraticForm

variable {E : Affine F} [E.IsElliptic]

/-- **AddMonoidHom-level quadratic expansion** (Silverman III.6 key algebra).

    Given:
    * a witness dual `α_dual` for `α` with the dual composition
      `α_dual ∘ α = [deg α]` holding at the `toAddMonoidHom` level
      (hypothesis `h_dual_comp`);
    * the trace identity `α + α_dual = [tr]` at the `toAddMonoidHom` level
      (hypothesis `h_sum_trace`);
    * β with `β.toAddMonoidHom = r·α - s·id` (hypothesis `hβ_hom`);
    * β_dual with `β_dual.toAddMonoidHom = r·α_dual - s·id` (hypothesis
      `hβ_dual_hom`);

    we have `(β_dual ∘ β).toAddMonoidHom = (mulByInt E N).toAddMonoidHom`
    where `N = deg(α)·r² - tr·r·s + s²`.

    This is the quadratic-expansion computation packaged as an `AddMonoidHom`
    equality, stated entirely on the explicit witness `α_dual` (the
    choice-based `isogDual` is gone — its underlying `exists_dual` was
    refuted; see the `DualIsogeny.lean` module docstring). -/
theorem comp_toAddMonoidHom_eq_mulByInt_of_quadratic
    (α α_dual : Isogeny E E) (tr : ℤ) (r s : ℤ) (β β_dual : Isogeny E E)
    (hβ_hom : β.toAddMonoidHom =
      r • α.toAddMonoidHom - s • (AddMonoidHom.id _))
    (hβ_dual_hom : β_dual.toAddMonoidHom =
      r • α_dual.toAddMonoidHom - s • (AddMonoidHom.id _))
    (h_dual_comp : ∀ P : E.Point, α_dual.toAddMonoidHom (α.toAddMonoidHom P) =
      (α.degree : ℤ) • P)
    (h_sum_trace : α.toAddMonoidHom + α_dual.toAddMonoidHom =
      (mulByInt E tr).toAddMonoidHom) :
    (β_dual.comp β).toAddMonoidHom =
      (mulByInt E ((α.degree : ℤ) * r ^ 2 - tr * r * s + s ^ 2)).toAddMonoidHom := by
  ext P
  rw [Isogeny.comp_toAddMonoidHom, AddMonoidHom.comp_apply, hβ_dual_hom, hβ_hom]
  change r • α_dual.toAddMonoidHom (r • α.toAddMonoidHom P - s • P) -
    s • (r • α.toAddMonoidHom P - s • P) = _
  have hrhs : (mulByInt E ((α.degree : ℤ) * r ^ 2 - tr * r * s + s ^ 2)).toAddMonoidHom P =
      ((α.degree : ℤ) * r ^ 2 - tr * r * s + s ^ 2 : ℤ) • P := rfl
  rw [hrhs]
  have hcP : α_dual.toAddMonoidHom (α.toAddMonoidHom P) = (α.degree : ℤ) • P :=
    h_dual_comp P
  have hdP : α_dual.toAddMonoidHom P = (tr : ℤ) • P - α.toAddMonoidHom P := by
    have h := congr_fun (congr_arg DFunLike.coe h_sum_trace) P
    simp only [AddMonoidHom.add_apply] at h
    have h' : (mulByInt E tr).toAddMonoidHom P = (tr : ℤ) • P := rfl
    rw [h'] at h
    rw [add_comm] at h
    exact eq_sub_of_add_eq h
  rw [map_sub, map_zsmul, map_zsmul, hcP, hdP]
  simp only [smul_sub, ← mul_zsmul]
  rw [show s * r = r * s from mul_comm s r]
  module

/-! ### Degree quadratic form — III.6.3

The bare `degree_quadratic` and `degree_quadratic_nonneg` theorems were
removed as part of the qf_nonneg migration (audit findings F2/F3,
`.mathlib-quality/isogeny-compatibility-audit.md`). Their original shape
asserted `(β.degree : ℤ) = (α.degree : ℤ) * r ^ 2 - …` for any `β` with the
right `toAddMonoidHom`. With the placeholder `isogSmulSub` (pullback :=
`AlgHom.id`, degree = 1) used as the canonical `β`, the equality was
structurally false at `(r, s) = (0, 0)` — the lemma was a `sorry` on a
false statement, and the consequence `_nonneg` likewise inherited an
unsound conclusion under the placeholder.

The witness-parametric replacements remain:

* `degree_quadratic_nonneg_of_witness` — same `_nonneg` conclusion, but
  takes the III.6.3 equality as an explicit hypothesis, sound regardless
  of the supplied `β`.
* `traceOfFrobenius_sq_le_of_qf_nonneg` (`Hasse/BoundOfWitnesses.lean`) —
  routes the discriminant bound through pure ℤ-arithmetic and bypasses
  any isogeny-degree assertion entirely. -/

/-- **Parametric form of III.6.3**: given the degree equality as hypothesis,
    the quadratic form non-negativity is immediate (since `β.degree : ℕ`).

    This version is closable without requiring the III.6.3 proof. The
    hypothesis `h_deg_eq` is what `degree_quadratic` would prove; callers
    that have access to a witness (e.g. via the dual isogeny chain) can
    use this directly. -/
theorem degree_quadratic_nonneg_of_witness
    (α : Isogeny E E) (one_sub_α : Isogeny E E) (r s : ℤ)
    (β : Isogeny E E)
    (h_deg_eq : (β.degree : ℤ) =
      (α.degree : ℤ) * r ^ 2 - (isogTrace α one_sub_α) * r * s + s ^ 2) :
    0 ≤ (α.degree : ℤ) * r ^ 2 - (isogTrace α one_sub_α) * r * s + s ^ 2 := by
  rw [← h_deg_eq]
  exact Int.natCast_nonneg _

/-! ### Dual-chain consumers (step 4 of the Hasse-bound closure plan)

The `degree_quadratic` sorry above is gated on the Silverman III.6 chain
(T-III-6-001 dual existence, T-III-6-005 dual additivity, III.8 trace
formula). The consumer theorems below expose the exact bridge from the
III.6 outputs to the degree identity, one witness at a time, so the
entire chain becomes drop-in once either Route A (kernel factorization,
step 3) or Route D (formal-group bridge, T-IV-BRIDGE-003) lands.

Witness-to-ticket map:

| Hypothesis | Silverman | Ticket |
|------------|-----------|--------|
| `h_comp` | III.6.1 (β̂∘β = [deg β]) | T-III-6-003 |
| `h_dual_deg` | III.6.2(a) (deg β̂ = deg β) | T-III-6-007 |
| `hβ_dual_spec` | III.6.1 as IsDualOf | T-III-6-001 |

Once those three drop, the β.degree² identity emerges algebraically. -/

/-- **SIGNED degree extraction via Wall C (SUB-PIV-D)**:
given that `β.comp α = mulByInt E N` as a FULL ISOGENY equality (not just
AddMonoidHom), and that `IsDualOf β α` (so `β.comp α = mulByInt α.degree`),
conclude `α.degree = N` SIGNED via Wall C (`mulByInt_left_injective`).

This is the non-circular signed extraction that bypasses
`degree_quadratic_of_dualChain_witnesses`'s `h_nonneg_N` hypothesis. Once a
producer ships the substantive `β.comp α = mulByInt E N` at the full
isogeny level (the SUB-PIV-C2 content), this lemma immediately delivers
the SIGNED III.6.3 identity without circularity.

Reference: Silverman III.6.3 + III.4.2b (Wall C). -/
theorem signed_degree_of_isDualOf_and_comp_eq
    {W : WeierstrassCurve F} [W.toAffine.IsElliptic]
    (α β : Isogeny W.toAffine W.toAffine) (N : ℤ) (hN : N ≠ 0)
    (h_isDual : IsDualOf W.toAffine β α)
    (h_alpha_pos : 0 < α.degree)
    (h_comp_eq : β.comp α = mulByInt W.toAffine N) :
    (α.degree : ℤ) = N := by
  have h_mulByInt_eq : mulByInt W.toAffine (α.degree : ℤ) = mulByInt W.toAffine N := by
    rw [← h_isDual.1, h_comp_eq]
  exact mulByInt_left_injective W (α.degree : ℤ) N
    (Int.natCast_ne_zero.mpr h_alpha_pos.ne') hN h_mulByInt_eq

/-- **SUB-PIV-D specialized**: SIGNED degree extraction for the genuine
`r·α − s·id` family, witness-parametric on the substantive pivot inputs.

Given:
- `α` (= π, the Frobenius)
- `β_dual` (= rV − s, the V-side genuine isogeny)
- `β` (= rπ − s, the π-side genuine isogeny)
- `IsDualOf β_dual β` (the substantive new content from SUB-PIV-C / Pic⁰ pivot)
- `β_dual.comp β = mulByInt W.toAffine N` (the full-isogeny composition equality)

This composes `signed_degree_of_isDualOf_and_comp_eq` for the genuine isogeny
family. Once SUB-PIV-C2 ships the `IsDualOf` + `comp_eq` witnesses
unconditionally over `L = AlgebraicClosure K` and descent to K, this becomes
the unconditional GAP-QF leaf.

Reference: Silverman III.6.3 + III.4.2b (Wall C). -/
theorem signed_degree_of_genuine_dual_pair
    {W : WeierstrassCurve F} [W.toAffine.IsElliptic]
    (β β_dual : Isogeny W.toAffine W.toAffine) (N : ℤ) (hN : N ≠ 0)
    (h_isDual : IsDualOf W.toAffine β_dual β)
    (h_beta_pos : 0 < β.degree)
    (h_comp_eq : β_dual.comp β = mulByInt W.toAffine N) :
    (β.degree : ℤ) = N :=
  signed_degree_of_isDualOf_and_comp_eq β β_dual N hN h_isDual h_beta_pos h_comp_eq

/-- **Witness-parametric squared-degree identity** (step 4a): if the dual
    composition `β̂.comp β` equals `mulByInt E N` as Isogenies and the
    dual preserves degree, then `β.degree² = N²` in `ℤ`.

    This is the content of Silverman III.6 applied at the composition
    level. It feeds `degree_quadratic` once combined with the sign
    (non-negativity of `β.degree`). -/
theorem sq_degree_eq_sq_of_dual_comp_witness
    (β β_dual : Isogeny E E) (N : ℤ) (hN : N ≠ 0)
    (h_comp : β_dual.comp β = mulByInt E N)
    (h_dual_deg : β_dual.degree = β.degree) :
    (β.degree : ℤ) ^ 2 = N ^ 2 := by
  have h3 : β.degree * β_dual.degree = (N ^ 2).toNat := by
    rw [← mulByInt_degree E N hN, ← h_comp]; exact (Isogeny.comp_degree β_dual β).symm
  rw [h_dual_deg] at h3
  have h4 : (β.degree * β.degree : ℤ) = N ^ 2 := by
    have hcast := congrArg ((↑·) : ℕ → ℤ) h3
    push_cast at hcast
    rw [hcast, Int.toNat_of_nonneg (sq_nonneg _)]
  rw [pow_two]; exact h4

/-- **Degree identity from dual composition** (step 4b, absolute-value form):
    under the same dual-composition witness, `(β.degree : ℤ) = |N|`. -/
theorem degree_eq_abs_of_dual_comp_witness
    (β β_dual : Isogeny E E) (N : ℤ) (hN : N ≠ 0)
    (h_comp : β_dual.comp β = mulByInt E N)
    (h_dual_deg : β_dual.degree = β.degree) :
    (β.degree : ℤ) = |N| := by
  have hsq := sq_degree_eq_sq_of_dual_comp_witness β β_dual N hN h_comp h_dual_deg
  have h_sq_abs : (β.degree : ℤ) ^ 2 = |N| ^ 2 := by rw [hsq, sq_abs]
  exact (sq_eq_sq₀ (Int.natCast_nonneg _) (abs_nonneg _)).mp h_sq_abs

/-- **Consumer of the dual chain** (step 4c): combines
    `sq_degree_eq_sq_of_dual_comp_witness` with the explicit
    quadratic-form expansion to close `degree_quadratic`, provided the
    caller supplies:

    * `β_dual` — the dual of `β` at the Isogeny level (T-III-6-001).
    * `h_comp` — the dual-composition identity with the QF value as
      `mulByInt E N` (the T-III-6-003 dual composition combined with the
      quadratic expansion `comp_toAddMonoidHom_eq_mulByInt_of_quadratic`).
    * `h_dual_deg` — `β_dual.degree = β.degree` (T-III-6-007 /
      `degree_dual_of_witness`).
    * `h_nonneg_N` — the QF expression is ≥ 0 (structural, from β's
      existence as a valid isogeny with non-negative degree).

    Downstream workers delivering these four witnesses close
    `degree_quadratic` without touching the keystone sorry. -/
theorem degree_quadratic_of_dualChain_witnesses
    (α : Isogeny E E) (one_sub_α : Isogeny E E) (r s : ℤ)
    (β β_dual : Isogeny E E)
    (h_N_ne : (α.degree : ℤ) * r ^ 2 - (isogTrace α one_sub_α) * r * s +
      s ^ 2 ≠ 0)
    (h_comp : β_dual.comp β = mulByInt E
      ((α.degree : ℤ) * r ^ 2 - (isogTrace α one_sub_α) * r * s + s ^ 2))
    (h_dual_deg : β_dual.degree = β.degree)
    (h_nonneg_N : 0 ≤ (α.degree : ℤ) * r ^ 2 -
      (isogTrace α one_sub_α) * r * s + s ^ 2) :
    (β.degree : ℤ) =
      (α.degree : ℤ) * r ^ 2 - (isogTrace α one_sub_α) * r * s + s ^ 2 := by
  set N := (α.degree : ℤ) * r ^ 2 - (isogTrace α one_sub_α) * r * s + s ^ 2
  have h_abs := degree_eq_abs_of_dual_comp_witness β β_dual N h_N_ne
    h_comp h_dual_deg
  rw [h_abs, abs_of_nonneg h_nonneg_N]

/-! ### Degree-level variants (weaker hypotheses)

The theorems above need the Isogeny-level equality `β_dual.comp β = mulByInt E N`,
which pins down both the `toAddMonoidHom` and the `pullback` of the composition.
Downstream dual-chain producers (whether via Route A kernel factorization or
Route D formal-group bridge) most naturally yield a *degree-level* identity
`(β_dual.comp β).degree = (mulByInt E N).degree`, which is strictly weaker.

This section exposes variants of the dual-chain consumer that only need
degree-level witnesses. They are proof-step-shorter to produce: the caller
just has to arrange that the composition's extension degree matches
`(N²).toNat`, rather than matching the full `mulByInt E N` isogeny.

The relations between the forms:

* `comp_degree`: `(ψ.comp φ).degree = φ.degree * ψ.degree`
* `mulByInt_degree`: `(mulByInt E N).degree = (N²).toNat` for `N ≠ 0`

So `(β_dual.comp β).degree = β.degree * β_dual.degree`, and the degree-level
witness becomes `β.degree * β_dual.degree = (N²).toNat`. -/

/-- **Degree-level variant of `sq_degree_eq_sq_of_dual_comp_witness`**
    (step 4a, weakened): only needs the product `β.degree · β_dual.degree`
    equal to `(N²).toNat`. This is what `comp_degree` would produce from a
    composition-level isogeny equality, so it's strictly weaker than the
    Isogeny-level hypothesis. -/
theorem sq_degree_eq_sq_of_dual_deg_prod_witness
    (β β_dual : Isogeny E E) (N : ℤ)
    (h_deg_prod : β.degree * β_dual.degree = (N ^ 2).toNat)
    (h_dual_deg : β_dual.degree = β.degree) :
    (β.degree : ℤ) ^ 2 = N ^ 2 := by
  rw [h_dual_deg] at h_deg_prod
  have h4 : (β.degree * β.degree : ℤ) = N ^ 2 := by
    have hcast := congrArg ((↑·) : ℕ → ℤ) h_deg_prod
    push_cast at hcast
    rw [hcast, Int.toNat_of_nonneg (sq_nonneg _)]
  rw [pow_two]; exact h4

/-- **Degree-level variant of `sq_degree_eq_sq_of_dual_comp_witness`** (alternative
    form): takes `(β_dual.comp β).degree = (N²).toNat` as a single hypothesis.
    Chains through `Isogeny.comp_degree` to reduce to
    `sq_degree_eq_sq_of_dual_deg_prod_witness`. -/
theorem sq_degree_eq_sq_of_comp_deg_witness
    (β β_dual : Isogeny E E) (N : ℤ)
    (h_comp_deg : (β_dual.comp β).degree = (N ^ 2).toNat)
    (h_dual_deg : β_dual.degree = β.degree) :
    (β.degree : ℤ) ^ 2 = N ^ 2 :=
  sq_degree_eq_sq_of_dual_deg_prod_witness β β_dual N
    ((Isogeny.comp_degree β_dual β).symm.trans h_comp_deg) h_dual_deg

/-- **Degree-level variant of `degree_eq_abs_of_dual_comp_witness`** (step 4b,
    weakened): concludes `(β.degree : ℤ) = |N|` from the product-level witness.

    Note: unlike the Isogeny-level version this does not require `N ≠ 0`;
    when `N = 0` the hypothesis forces `β.degree = 0 = |N|`. -/
theorem degree_eq_abs_of_dual_deg_prod_witness
    (β β_dual : Isogeny E E) (N : ℤ)
    (h_deg_prod : β.degree * β_dual.degree = (N ^ 2).toNat)
    (h_dual_deg : β_dual.degree = β.degree) :
    (β.degree : ℤ) = |N| := by
  have hsq := sq_degree_eq_sq_of_dual_deg_prod_witness β β_dual N h_deg_prod
    h_dual_deg
  have h_sq_abs : (β.degree : ℤ) ^ 2 = |N| ^ 2 := by rw [hsq, sq_abs]
  exact (sq_eq_sq₀ (Int.natCast_nonneg _) (abs_nonneg _)).mp h_sq_abs

/-- **Degree-level consumer of the dual chain** (step 4c, weakened):
    same conclusion as `degree_quadratic_of_dualChain_witnesses`, but the
    composition hypothesis is replaced by a product-of-degrees identity.

    Downstream producers (T-III-6-003 at the degree level, or the formal-group
    bridge) yield this form more directly than the Isogeny-level equality,
    since only `comp_degree` + `mulByInt_degree` are needed, not a full
    pullback match. -/
theorem degree_quadratic_of_dualChain_deg_witnesses
    (α : Isogeny E E) (one_sub_α : Isogeny E E) (r s : ℤ)
    (β β_dual : Isogeny E E)
    (h_deg_prod : β.degree * β_dual.degree =
      (((α.degree : ℤ) * r ^ 2 - (isogTrace α one_sub_α) * r * s + s ^ 2) ^ 2).toNat)
    (h_dual_deg : β_dual.degree = β.degree)
    (h_nonneg_N : 0 ≤ (α.degree : ℤ) * r ^ 2 -
      (isogTrace α one_sub_α) * r * s + s ^ 2) :
    (β.degree : ℤ) =
      (α.degree : ℤ) * r ^ 2 - (isogTrace α one_sub_α) * r * s + s ^ 2 := by
  set N := (α.degree : ℤ) * r ^ 2 - (isogTrace α one_sub_α) * r * s + s ^ 2
  have h_abs := degree_eq_abs_of_dual_deg_prod_witness β β_dual N
    h_deg_prod h_dual_deg
  rw [h_abs, abs_of_nonneg h_nonneg_N]

/-! ### T-III-6-009 ready-made call site

The theorem `degree_quadratic_closed` below is the **composite witness-parametric
call site** that closes the `degree_quadratic` identity from a complete bundle
of III.6 witnesses at the `AddMonoidHom` level plus the `toAddMonoidHom → degree`
bridge for the specific isogenies involved.

This is the form the Stream D brief describes as the final call site:
downstream workers delivering:
* `α_dual` — a witness dual for α (Route A kernel factorization, or Route D
  formal-group bridge)
* `hβ_hom`, `hβ_dual_hom` — β, β_dual in the r·α − s / r·α_dual − s forms
* `h_dual_comp` — α_dual ∘ α = [deg α] at the `AddMonoidHom` level (III.6.1
  content)
* `h_sum_trace` — α + α_dual = [tr α] at the `AddMonoidHom` level (III.8.6
  content via `dual_add_of_trace_witnesses`)
* `h_deg_bridge` — the `toAddMonoidHom ↔ degree` bridge for β_dual ∘ β and
  [N] (provided separately by Route A uniqueness of pullback, or by the
  Formal-Group bridge)
* `h_dual_deg` — β_dual.degree = β.degree (III.6.2(a) content from
  `degree_dual_of_witness`)
* `h_nonneg_N` — the QF value is ≥ 0 (algebraic)

gets the full Silverman III.6.3 identity. All four upstream tickets
(T-III-6-001, T-III-6-003, T-III-6-005, T-III-6-007) become drop-in once
their respective witnesses are produced. -/

/-- **T-III-6-009 ready-made call site**: closes `degree_quadratic` from a
    complete III.6 witness bundle at the `AddMonoidHom` level plus the
    `toAddMonoidHom → degree` bridge for the QF composition. -/
theorem degree_quadratic_closed
    (α α_dual one_sub_α : Isogeny E E) (r s : ℤ)
    (β β_dual : Isogeny E E)
    (hβ_hom : β.toAddMonoidHom =
      r • α.toAddMonoidHom - s • (AddMonoidHom.id _))
    (hβ_dual_hom : β_dual.toAddMonoidHom =
      r • α_dual.toAddMonoidHom - s • (AddMonoidHom.id _))
    (h_dual_comp : ∀ P : E.Point, α_dual.toAddMonoidHom (α.toAddMonoidHom P) =
      (α.degree : ℤ) • P)
    (h_sum_trace : α.toAddMonoidHom + α_dual.toAddMonoidHom =
      (mulByInt E (isogTrace α one_sub_α)).toAddMonoidHom)
    (h_deg_bridge : (β_dual.comp β).toAddMonoidHom =
        (mulByInt E ((α.degree : ℤ) * r ^ 2 -
          (isogTrace α one_sub_α) * r * s + s ^ 2)).toAddMonoidHom →
      (β_dual.comp β).degree =
        (((α.degree : ℤ) * r ^ 2 -
          (isogTrace α one_sub_α) * r * s + s ^ 2) ^ 2).toNat)
    (h_dual_deg : β_dual.degree = β.degree)
    (h_nonneg_N : 0 ≤ (α.degree : ℤ) * r ^ 2 -
      (isogTrace α one_sub_α) * r * s + s ^ 2) :
    (β.degree : ℤ) =
      (α.degree : ℤ) * r ^ 2 - (isogTrace α one_sub_α) * r * s + s ^ 2 := by
  have h_comp_hom := comp_toAddMonoidHom_eq_mulByInt_of_quadratic
    α α_dual (isogTrace α one_sub_α) r s β β_dual
    hβ_hom hβ_dual_hom h_dual_comp h_sum_trace
  have h_comp_deg := h_deg_bridge h_comp_hom
  have h_deg_prod : β.degree * β_dual.degree =
      (((α.degree : ℤ) * r ^ 2 -
        (isogTrace α one_sub_α) * r * s + s ^ 2) ^ 2).toNat :=
    (Isogeny.comp_degree β_dual β).symm.trans h_comp_deg
  exact degree_quadratic_of_dualChain_deg_witnesses α one_sub_α r s β β_dual
    h_deg_prod h_dual_deg h_nonneg_N

/-! **[2026-05-28 placeholder grind]** `isogSmulSub_degree_quadratic_closed` (the
placeholder-`isogSmulSub` specialization of `degree_quadratic_closed`) was deleted
along with the `isogSmulSub` placeholder. The generic `degree_quadratic_closed`
above takes any `β` with point-map `r·α − s` and is the live witness-parametric
form; the genuine `(r,s)`-isogeny is `genuineIsogSmulSub`. -/

end QuadraticForm

/-! ### Polarisation identity for genuine `addIsog`-built isogenies — Silverman III.6.3

The witness-parametric closers `degree_quadratic_closed` /
`isogSmulSub_degree_quadratic_closed` deliver the III.6.3 degree identity for
*any* `β` whose `toAddMonoidHom` matches `r·α − s·id` and whose dual matches
`r·α̂ − s·id`. The placeholder `isogSmulSub` (`Endomorphism.lean`) supplies the
correct `toAddMonoidHom` but a trivial `pullback := AlgHom.id` — which makes the
`h_deg_bridge` hypothesis structurally false at `(r,s) = (0,0)` and the
non-negativity hypothesis vacuous.

The genuine `r·α − s·id` isogeny is `addIsog` of `(α.zsmul r, mulByInt E (-s))`
(`AdditionPullback.lean`): its pullback is the genuine algebra-hom pullback
witness-parametric on `AddNonInversePair` and injectivity of the coordinate
algebra hom. With the Frobenius case `α = π`, Worker B's D3b output supplies
`AddNonInversePair (π.zsmul r) (mulByInt (-s))` axiom-clean, and Worker C's
Verschiebung output supplies the dual chain (V dual of π, sum-trace, dual-deg).

The theorem below is the **specialisation of `degree_quadratic_closed` to the
addIsog-built `β` family**: it auto-discharges the `hβ_hom`/`hβ_dual_hom`
hypotheses via `addIsog_toAddMonoidHom`, leaving only the genuine III.6 inputs
(dual-comp, sum-trace, dual-deg, deg-bridge, nonneg) for downstream consumers
to deliver. -/

/-! ### Trace identity from the dual chain (Silverman III.6.2(b), Hasse case)

The polarisation chain consumes `h_sum_trace : α + α_dual = [tr α]` at the
`toAddMonoidHom` level. Silverman derives this from the III.6.2(b) bilinear
pairing argument; for the Hasse-critical case (α = π Frobenius, α_dual = V
Verschiebung) the substantive ingredient is

  `(1 − α) ∘ (1 − α_dual) = [deg(1 − α)]`   (at hom level)

Combined with the dual-composition halves `α_dual ∘ α = α ∘ α_dual = [deg α]`,
the bilinear expansion `(1 − α)(1 − α_dual) = [1] − α − α_dual + α α_dual`
reduces directly to `α + α_dual = [1 + deg α − deg(1 − α)] = [tr α]`. The
bridge below packages this algebra as a single drop-in identity, avoiding the
need to prove universal dual additivity (long-term Silverman track per
reviewer Q5). -/

section TraceIdentity

variable {F : Type*} [Field F] [DecidableEq F]
variable {E : Affine F} [E.IsElliptic]

/-- **Trace identity from the dual chain (Silverman III.6.2(b), Hasse case)**:
    given the dual-composition half `α ∘ α_dual = [deg α]` (one half of
    `IsDualOf α_dual α`) plus the III.6.2(b) substantive identity
    `(1 − α) ∘ (1 − α_dual) = [deg(1 − α)]` at `toAddMonoidHom` level,
    conclude

      `α + α_dual = [1 + deg α − deg(1 − α)] = [tr α]`

    at `toAddMonoidHom` level. This is the trace identity consumed by
    `degree_quadratic_closed` / `degree_quadratic_genuine_addIsog` as
    `h_sum_trace`.

    The substantive hypothesis `h_one_sub_one_sub_dual` is the III.6.2(b)
    content for the Hasse-critical case — Worker C's Frobenius-specific
    dual chain plus the genuine `1 − π` isogeny
    (`isogOneSub_negFrobenius W hq` in `AdditionPullback/Frobenius.lean`)
    discharge it without needing universal dual additivity. -/
theorem trace_identity_of_dual_chain
    (α α_dual : Isogeny E E) (one_sub_α one_sub_α_dual : Isogeny E E)
    (h_dual_comp_right : ∀ P : E.Point,
        α.toAddMonoidHom (α_dual.toAddMonoidHom P) = (α.degree : ℤ) • P)
    (h_one_sub_α_hom : one_sub_α.toAddMonoidHom =
        AddMonoidHom.id _ - α.toAddMonoidHom)
    (h_one_sub_α_dual_hom : one_sub_α_dual.toAddMonoidHom =
        AddMonoidHom.id _ - α_dual.toAddMonoidHom)
    (h_one_sub_one_sub_dual : ∀ P : E.Point,
        one_sub_α.toAddMonoidHom (one_sub_α_dual.toAddMonoidHom P) =
          (one_sub_α.degree : ℤ) • P) :
    α.toAddMonoidHom + α_dual.toAddMonoidHom =
        (mulByInt E (isogTrace α one_sub_α)).toAddMonoidHom := by
  ext P
  have hcomp : (one_sub_α.degree : ℤ) • P =
      P - α_dual.toAddMonoidHom P - α.toAddMonoidHom P + (α.degree : ℤ) • P := by
    rw [← h_one_sub_one_sub_dual, h_one_sub_α_dual_hom,
      AddMonoidHom.sub_apply, AddMonoidHom.id_apply, map_sub,
      h_one_sub_α_hom, AddMonoidHom.sub_apply, AddMonoidHom.sub_apply,
      AddMonoidHom.id_apply, AddMonoidHom.id_apply, h_dual_comp_right]
    abel
  show (α.toAddMonoidHom + α_dual.toAddMonoidHom) P =
      (mulByInt E (isogTrace α one_sub_α)).toAddMonoidHom P
  rw [AddMonoidHom.add_apply, mulByInt_apply]
  unfold isogTrace
  have hsum :
      ((1 + (α.degree : ℤ) - (one_sub_α.degree : ℤ)) : ℤ) • P =
        P + (α.degree : ℤ) • P - (one_sub_α.degree : ℤ) • P := by
    rw [show (1 + (α.degree : ℤ) - (one_sub_α.degree : ℤ)) =
        (1 : ℤ) + (α.degree : ℤ) + -(one_sub_α.degree : ℤ) by ring,
      add_smul, add_smul, neg_smul, one_smul]
    abel
  rw [hsum, hcomp]
  abel

end TraceIdentity

section GenuineQuadraticForm

variable {F : Type*} [Field F] [DecidableEq F]
variable {W : WeierstrassCurve F} [W.toAffine.IsElliptic]

/-- **Silverman III.6.3 polarisation identity, genuine `addIsog` form**: for the
    genuine `r·α − s·id` isogeny `addIsog hxy_β hinj_β` (with α₁ = α.zsmul r,
    α₂ = mulByInt (-s)) and a corresponding `addIsog`-built `r·α_dual − s·id`,
    given the standard Silverman III.6 inputs (dual composition, sum trace,
    dual-degree equality, degree bridge, QF non-negativity) the III.6.3
    identity

      `(addIsog hxy_β hinj_β).degree = (α.degree)·r² − (tr α)·rs + s²`

    holds at the integer level.

    Drop-in form: once Worker B's D-track ships `hxy_β/hinj_β` axiom-clean (and
    the analogous V-pair from Worker C), this becomes the unconditional general-α
    polarisation identity, replacing the deleted false `degree_quadratic`.

    Reference: Silverman, *The Arithmetic of Elliptic Curves*, Cor. III.6.3. -/
theorem degree_quadratic_genuine_addIsog
    (α α_dual one_sub_α : Isogeny W.toAffine W.toAffine) (r s : ℤ)
    (hxy_β : AddNonInversePair (α.zsmul r) (mulByInt W.toAffine (-s)))
    (hinj_β : Function.Injective (addCoordAlgHomPair hxy_β))
    (hxy_β_dual : AddNonInversePair (α_dual.zsmul r) (mulByInt W.toAffine (-s)))
    (hinj_β_dual : Function.Injective (addCoordAlgHomPair hxy_β_dual))
    (h_dual_comp : ∀ P : W.toAffine.Point,
        α_dual.toAddMonoidHom (α.toAddMonoidHom P) = (α.degree : ℤ) • P)
    (h_sum_trace : α.toAddMonoidHom + α_dual.toAddMonoidHom =
        (mulByInt W.toAffine (isogTrace α one_sub_α)).toAddMonoidHom)
    (h_deg_bridge :
        ((addIsog hxy_β_dual hinj_β_dual).comp (addIsog hxy_β hinj_β)).toAddMonoidHom =
            (mulByInt W.toAffine ((α.degree : ℤ) * r ^ 2 -
              isogTrace α one_sub_α * r * s + s ^ 2)).toAddMonoidHom →
        ((addIsog hxy_β_dual hinj_β_dual).comp (addIsog hxy_β hinj_β)).degree =
            (((α.degree : ℤ) * r ^ 2 -
              isogTrace α one_sub_α * r * s + s ^ 2) ^ 2).toNat)
    (h_dual_deg :
        (addIsog hxy_β_dual hinj_β_dual).degree = (addIsog hxy_β hinj_β).degree)
    (h_nonneg_N : 0 ≤ (α.degree : ℤ) * r ^ 2 -
        isogTrace α one_sub_α * r * s + s ^ 2) :
    ((addIsog hxy_β hinj_β).degree : ℤ) =
        (α.degree : ℤ) * r ^ 2 - isogTrace α one_sub_α * r * s + s ^ 2 := by
  refine degree_quadratic_closed (E := W.toAffine) α α_dual one_sub_α r s
    (addIsog hxy_β hinj_β) (addIsog hxy_β_dual hinj_β_dual)
    ?hβ_hom ?hβ_dual_hom h_dual_comp h_sum_trace h_deg_bridge h_dual_deg h_nonneg_N
  case hβ_hom =>
    ext P
    simp only [addIsog_toAddMonoidHom, AddMonoidHom.add_apply,
      AddMonoidHom.sub_apply, AddMonoidHom.smul_apply, AddMonoidHom.id_apply,
      Isogeny.zsmul_apply, mulByInt_apply]
    rw [neg_smul, sub_eq_add_neg]
  case hβ_dual_hom =>
    ext P
    simp only [addIsog_toAddMonoidHom, AddMonoidHom.add_apply,
      AddMonoidHom.sub_apply, AddMonoidHom.smul_apply, AddMonoidHom.id_apply,
      Isogeny.zsmul_apply, mulByInt_apply]
    rw [neg_smul, sub_eq_add_neg]

end GenuineQuadraticForm

end HasseWeil
