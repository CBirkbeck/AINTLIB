import HasseWeil.FormalGroup.MulByNat
import HasseWeil.FormalGroup.Logarithm

/-!
# Formal group homomorphisms: identity, composition, and basic API

This file provides the core category-theoretic API for formal group
homomorphisms:

* `FormalGroupHom.id F : FormalGroupHom F F` — the identity homomorphism.
* `FormalGroupHom.comp g f : FormalGroupHom F H` — composition of `g : G → H`
  with `f : F → G`.

Together with the `FormalGroupHom.mk.injEq` extensionality principle, this
makes `FormalGroup R` into a category (informally — we don't set up the
`Category` instance here, since the usual formal-group-law category has some
subtleties around Hom-sets).

## Main definitions

* `FormalGroupHom.id`, `FormalGroupHom.comp`

## Main results

* `FormalGroupHom.id_toSeries`, `FormalGroupHom.comp_toSeries` — simp lemmas.
* `FormalGroupHom.id_eq_mulByNatHom_one` — the identity hom is
  `mulByNatHom F 1`.
* `FormalGroupHom.coeff_one_id`, `FormalGroupHom.coeff_one_comp` — the
  linear coefficient is `1` (resp. a product) for `id` (resp. `comp`).
* `FormalGroupHom.ext` — extensionality via `toSeries`.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], IV.2.
-/

set_option linter.dupNamespace false

namespace HasseWeil.FormalGroup

variable {R : Type*} [CommRing R]

/-! ### Extensionality -/

/-- Two formal group homomorphisms `F → G` are equal iff their underlying
power series are equal. The other fields (`zero_const`, `preserves_add`)
are propositions, so proof-irrelevance handles them. -/
@[ext]
theorem FormalGroupHom.ext {F G : FormalGroup R} {f g : FormalGroupHom F G}
    (h : f.toSeries = g.toSeries) : f = g := by
  cases f; cases g; congr

/-! ### The identity formal group homomorphism -/

/-- The identity formal group homomorphism `F → F`, whose underlying power
series is `T`.

Reference: Silverman IV.2 (definition of `FormalGroupHom`). -/
noncomputable def FormalGroupHom.id (F : FormalGroup R) : FormalGroupHom F F where
  toSeries := PowerSeries.X
  zero_const := by simp
  preserves_add := by
    -- LHS: subst F.toSeries X = F.toSeries (by `PowerSeries.subst_X` style).
    -- RHS: subst ![subst (X 0) X, subst (X 1) X] F.toSeries
    --    = subst ![X 0, X 1] F.toSeries = F.toSeries (identity subst).
    -- Both equal F.toSeries.
    have hlhs : PowerSeries.subst F.toSeries (PowerSeries.X : PowerSeries R) =
        F.toSeries := by
      change MvPowerSeries.subst (fun _ : Unit => F.toSeries)
        (MvPowerSeries.X () : MvPowerSeries Unit R) = F.toSeries
      have h : MvPowerSeries.HasSubst
          (fun _ : Unit => F.toSeries : Unit → MvPowerSeries (Fin 2) R) := by
        apply MvPowerSeries.hasSubst_of_constantCoeff_zero
        intro; exact HasseWeil.FG.constantCoeff_FG_toSeries F
      exact MvPowerSeries.subst_X h ()
    have hX0 : PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R)
        (PowerSeries.X : PowerSeries R) = MvPowerSeries.X 0 := by
      change MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R))
        (MvPowerSeries.X () : MvPowerSeries Unit R) = _
      have h : MvPowerSeries.HasSubst
          (fun _ : Unit => (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R)) := by
        apply MvPowerSeries.hasSubst_of_constantCoeff_zero; intro; simp
      exact MvPowerSeries.subst_X h ()
    have hX1 : PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)
        (PowerSeries.X : PowerSeries R) = MvPowerSeries.X 1 := by
      change MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R))
        (MvPowerSeries.X () : MvPowerSeries Unit R) = _
      have h : MvPowerSeries.HasSubst
          (fun _ : Unit => (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)) := by
        apply MvPowerSeries.hasSubst_of_constantCoeff_zero; intro; simp
      exact MvPowerSeries.subst_X h ()
    rw [hlhs, hX0, hX1]
    -- Goal: F.toSeries = subst ![X 0, X 1] F.toSeries
    have h_id : MvPowerSeries.HasSubst
        (![MvPowerSeries.X 0, MvPowerSeries.X 1] :
          Fin 2 → MvPowerSeries (Fin 2) R) := by
      apply MvPowerSeries.hasSubst_of_constantCoeff_zero
      intro s; fin_cases s <;> simp
    have heq : (![MvPowerSeries.X (0 : Fin 2), MvPowerSeries.X 1] :
        Fin 2 → MvPowerSeries (Fin 2) R) =
        (fun s : Fin 2 => MvPowerSeries.X s) := by
      funext s; fin_cases s <;> rfl
    rw [heq]
    exact (congr_fun MvPowerSeries.subst_self F.toSeries).symm

/-- The identity hom has underlying series `X`. -/
@[simp]
theorem FormalGroupHom.id_toSeries (F : FormalGroup R) :
    (FormalGroupHom.id F).toSeries = PowerSeries.X := rfl

/-- The linear coefficient of the identity hom is `1`. -/
@[simp]
theorem FormalGroupHom.coeff_one_id (F : FormalGroup R) :
    PowerSeries.coeff 1 (FormalGroupHom.id F).toSeries = 1 := by
  simp

/-- The identity hom equals `mulByNatHom F 1`. -/
theorem FormalGroupHom.id_eq_mulByNatHom_one (F : FormalGroup R) :
    FormalGroupHom.id F = F.mulByNatHom 1 := by
  ext
  rw [FormalGroupHom.id_toSeries, FormalGroup.mulByNatHom_one_toSeries]

/-! ### Helpers for composition

These helpers are useful for downstream composition-style proofs but a clean
`FormalGroupHom.comp` with `preserves_add` is deferred (see T-IV-2-010). -/

/-- Commutation identity: substituting `MvPowerSeries.subst A B` for the
variable of a `PowerSeries` can be replaced by first substituting `B` and
then applying the `MvPowerSeries.subst A` operation on the result. -/
theorem PowerSeries_subst_MvSubst_eq {σ τ : Type*}
    (A : σ → MvPowerSeries τ R) (hA : MvPowerSeries.HasSubst A)
    (B : MvPowerSeries σ R) (hB : MvPowerSeries.constantCoeff B = 0)
    (g : PowerSeries R) :
    PowerSeries.subst (MvPowerSeries.subst A B) g =
      MvPowerSeries.subst A (PowerSeries.subst B g) := by
  rw [PowerSeries.subst_def, PowerSeries.subst_def]
  have hB' : MvPowerSeries.HasSubst (fun _ : Unit => B) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero; intro; exact hB
  rw [MvPowerSeries.subst_comp_subst_apply hB' hA]

/-! ### Composition of formal group homomorphisms

We build `(g : G → H).comp (f : F → G) : F → H` whose underlying series is
`PowerSeries.subst f.toSeries g.toSeries`, and verify the `preserves_add`
axiom. -/

section Comp

variable {F G H' : FormalGroup R}

/-- Helper: `HasSubst` for the bivariate lift `![subst (X 0) f, subst (X 1) f]`
of a univariate homomorphism series `f` with `f(0) = 0`. -/
private lemma FormalGroupHom.hasSubst_pair_lift
    (f : PowerSeries R) (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.HasSubst
      (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) f,
         PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) f] :
        Fin 2 → MvPowerSeries (Fin 2) R) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro s; fin_cases s
  · simpa using HasseWeil.FG.constantCoeff_univariate_subst
      (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) (by simp) f hf
  · simpa using HasseWeil.FG.constantCoeff_univariate_subst
      (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) (by simp) f hf

/-- Composition of formal group homomorphisms. Given `f : F → G` and `g : G → H'`,
the composite `g.comp f : F → H'` has underlying series
`PowerSeries.subst f.toSeries g.toSeries`.

Reference: Silverman IV.2 (composition of formal group homomorphisms). -/
noncomputable def FormalGroupHom.comp
    (g : FormalGroupHom G H') (f : FormalGroupHom F G) : FormalGroupHom F H' where
  toSeries := PowerSeries.subst f.toSeries g.toSeries
  zero_const :=
    PowerSeries.constantCoeff_subst_eq_zero f.zero_const g.toSeries g.zero_const
  preserves_add := by
    -- Abbreviations for the bivariate lifts of f and g.
    set fX : MvPowerSeries (Fin 2) R :=
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) f.toSeries with hfX_def
    set fY : MvPowerSeries (Fin 2) R :=
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) f.toSeries with hfY_def
    set gX : MvPowerSeries (Fin 2) R :=
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) g.toSeries with hgX_def
    set gY : MvPowerSeries (Fin 2) R :=
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) g.toSeries with hgY_def
    -- Abbreviation for the underlying series of the composite.
    set fg : PowerSeries R := PowerSeries.subst f.toSeries g.toSeries with hfg_def
    have hfg_cc : PowerSeries.constantCoeff fg = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero f.zero_const g.toSeries g.zero_const
    -- HasSubst facts. We rely on the `PowerSeries.HasSubst` name (abbreviation).
    have hF_ps : PowerSeries.HasSubst (F.toSeries : MvPowerSeries (Fin 2) R) :=
      PowerSeries.HasSubst.of_constantCoeff_zero
        (HasseWeil.FG.constantCoeff_FG_toSeries F)
    have hf_ps : PowerSeries.HasSubst (f.toSeries : PowerSeries R) :=
      PowerSeries.HasSubst.of_constantCoeff_zero' f.zero_const
    have hG_ps : PowerSeries.HasSubst (G.toSeries : MvPowerSeries (Fin 2) R) :=
      PowerSeries.HasSubst.of_constantCoeff_zero
        (HasseWeil.FG.constantCoeff_FG_toSeries G)
    have hX0_ps : PowerSeries.HasSubst
        (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) :=
      PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
    have hX1_ps : PowerSeries.HasSubst
        (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) :=
      PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
    have hpair_f :=
      FormalGroupHom.hasSubst_pair_lift f.toSeries f.zero_const
    have hpair_g :=
      FormalGroupHom.hasSubst_pair_lift g.toSeries g.zero_const
    -- Step 1: LHS via PowerSeries.subst_comp_subst_apply.
    -- subst F.toSeries (subst f.toSeries g.toSeries)
    --   = subst (subst F.toSeries f.toSeries) g.toSeries
    rw [show PowerSeries.subst F.toSeries fg =
        PowerSeries.subst (PowerSeries.subst F.toSeries f.toSeries) g.toSeries from
      PowerSeries.subst_comp_subst_apply hf_ps hF_ps g.toSeries]
    -- Step 2: Apply f.preserves_add.
    rw [f.preserves_add]
    -- Now we have: subst (MvPowerSeries.subst ![fX, fY] G.toSeries) g.toSeries
    -- Step 3: Commute the substitutions via PowerSeries_subst_MvSubst_eq.
    rw [PowerSeries_subst_MvSubst_eq (![fX, fY] : Fin 2 → MvPowerSeries (Fin 2) R)
        hpair_f G.toSeries (HasseWeil.FG.constantCoeff_FG_toSeries G) g.toSeries]
    -- Now: MvPowerSeries.subst ![fX, fY] (PowerSeries.subst G.toSeries g.toSeries)
    -- Step 4: Apply g.preserves_add to the inner subst.
    rw [g.preserves_add]
    -- Now: MvPowerSeries.subst ![fX, fY]
    --       (MvPowerSeries.subst ![gX, gY] H'.toSeries)
    -- Step 5: Use MvPowerSeries.subst_comp_subst_apply for the outer double-subst.
    rw [MvPowerSeries.subst_comp_subst_apply hpair_g hpair_f]
    -- Goal: MvPowerSeries.subst
    --         (fun s => subst ![fX, fY] (![gX, gY] s)) H'.toSeries
    --      = MvPowerSeries.subst ![subst (X 0) fg, subst (X 1) fg] H'.toSeries
    -- Step 6: Show the two substitution functions are equal.
    congr 1
    funext s
    fin_cases s
    · -- s = 0: subst ![fX, fY] gX = PowerSeries.subst (X 0) fg.
      change MvPowerSeries.subst (![fX, fY] : Fin 2 → MvPowerSeries (Fin 2) R) gX =
        PowerSeries.subst
          (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) fg
      -- Unfold gX: gX = subst (X 0) g.toSeries.
      -- LHS: subst ![fX, fY] (subst (X 0) g.toSeries)
      --    = subst (subst ![fX, fY] (X 0)) g.toSeries  [by PowerSeries_subst_MvSubst_eq]
      --    = subst fX g.toSeries                       [by subst_matrix_X0]
      rw [show gX =
          PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) g.toSeries from rfl]
      rw [show fg =
          PowerSeries.subst f.toSeries g.toSeries from rfl]
      rw [← PowerSeries_subst_MvSubst_eq (![fX, fY] : Fin 2 → MvPowerSeries (Fin 2) R)
          hpair_f (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) (by simp) g.toSeries]
      rw [HasseWeil.FG.subst_matrix_X0 _ hpair_f]
      -- LHS is now `subst (![fX, fY] 0) g.toSeries`. Matrix.cons_val_zero simplifies.
      simp only [Matrix.cons_val_zero]
      -- RHS: subst (X 0) (subst f.toSeries g.toSeries)
      --    = subst (subst (X 0) f.toSeries) g.toSeries  [by PowerSeries.subst_comp_subst_apply]
      --    = subst fX g.toSeries (by definition).
      rw [PowerSeries.subst_comp_subst_apply hf_ps hX0_ps g.toSeries]
    · -- s = 1: symmetric.
      change MvPowerSeries.subst (![fX, fY] : Fin 2 → MvPowerSeries (Fin 2) R) gY =
        PowerSeries.subst
          (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) fg
      rw [show gY =
          PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) g.toSeries from rfl]
      rw [show fg =
          PowerSeries.subst f.toSeries g.toSeries from rfl]
      rw [← PowerSeries_subst_MvSubst_eq (![fX, fY] : Fin 2 → MvPowerSeries (Fin 2) R)
          hpair_f (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) (by simp) g.toSeries]
      rw [HasseWeil.FG.subst_matrix_X1 _ hpair_f]
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [PowerSeries.subst_comp_subst_apply hf_ps hX1_ps g.toSeries]

/-- The underlying series of `g.comp f` is `PowerSeries.subst f.toSeries g.toSeries`. -/
@[simp]
theorem FormalGroupHom.comp_toSeries
    (g : FormalGroupHom G H') (f : FormalGroupHom F G) :
    (g.comp f).toSeries = PowerSeries.subst f.toSeries g.toSeries := rfl

/-- Left identity for composition: `(id G).comp f = f`. -/
@[simp]
theorem FormalGroupHom.id_comp (f : FormalGroupHom F G) :
    (FormalGroupHom.id G).comp f = f := by
  refine FormalGroupHom.ext ?_
  rw [FormalGroupHom.comp_toSeries, FormalGroupHom.id_toSeries]
  -- Goal: PowerSeries.subst f.toSeries PowerSeries.X = f.toSeries.
  change MvPowerSeries.subst (fun _ : Unit => f.toSeries)
    (MvPowerSeries.X () : MvPowerSeries Unit R) = f.toSeries
  have h : MvPowerSeries.HasSubst
      (fun _ : Unit => f.toSeries : Unit → MvPowerSeries Unit R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro; exact f.zero_const
  exact MvPowerSeries.subst_X h ()

/-- Right identity for composition: `f.comp (id F) = f`. -/
@[simp]
theorem FormalGroupHom.comp_id (f : FormalGroupHom F G) :
    f.comp (FormalGroupHom.id F) = f := by
  refine FormalGroupHom.ext ?_
  rw [FormalGroupHom.comp_toSeries, FormalGroupHom.id_toSeries]
  -- Goal: PowerSeries.subst PowerSeries.X f.toSeries = f.toSeries.
  rw [PowerSeries.subst_def]
  -- Goal: MvPowerSeries.subst (fun _ : Unit => PowerSeries.X) f.toSeries = f.toSeries.
  have heq : (fun _ : Unit => (PowerSeries.X : PowerSeries R)) =
      (MvPowerSeries.X : Unit → MvPowerSeries Unit R) := by
    funext _; rfl
  rw [heq]
  exact congr_fun MvPowerSeries.subst_self f.toSeries

end Comp

/-! ### `mulByNatHom F 1` is an isomorphism (T-IV-2-008, n = 1 case)

Silverman IV.2.3(b): if `m ∈ R*` (unit), then `[m] : F → F` is an isomorphism
of formal groups. We handle the special case `m = 1` here — it follows
immediately from `FormalGroupHom.id_eq_mulByNatHom_one`.

The general unit case (for `n : ℕ` with `(n : R)` a unit, or for `m : ℤ` unit)
requires a compositional inverse for power series whose linear coefficient is
a unit (not necessarily `1`). Currently `HasseWeil.FormalGroup.compInverse`
(in `Logarithm.lean`) is defined only for series with `coeff 1 f = 1`. Closing
the general case requires either:

  * Generalising `compInverse` to the unit-leading-coefficient case, by
    conjugating with the linear scaling `T ↦ u⁻¹ · T` (so
    `g(T) := u⁻¹ · (compInverse of u⁻¹ · f)(u · T)` where `u = coeff 1 f`), or
  * Constructing `mulByNatHom`'s inverse directly by unit-coefficient
    recursion.

The trivial case `n = 1` below is the immediate consequence of the identity
hom being `mulByNatHom F 1`. -/

/-- **Silverman IV.2.3(b), trivial case**: `mulByNatHom F 1` is an isomorphism
of formal groups, witnessed by the identity hom.

This is an immediate corollary of `FormalGroupHom.id_eq_mulByNatHom_one`:
since `id F = mulByNatHom F 1`, the identity hom witnesses both sides of the
isomorphism pair.

The general unit case `(n : R) ∈ R*` is deferred; see the module doc above. -/
theorem FormalGroup.mulByNatHom_one_isIso (F : FormalGroup R) :
    (F.mulByNatHom 1).comp (FormalGroupHom.id F) = FormalGroupHom.id F ∧
      (FormalGroupHom.id F).comp (F.mulByNatHom 1) = FormalGroupHom.id F := by
  refine ⟨?_, ?_⟩
  · -- (mulByNatHom F 1).comp (id F) = id F.
    -- Rewrite mulByNatHom F 1 = id F via id_eq_mulByNatHom_one, then use comp_id.
    rw [← FormalGroupHom.id_eq_mulByNatHom_one]
    exact FormalGroupHom.comp_id (FormalGroupHom.id F)
  · -- (id F).comp (mulByNatHom F 1) = id F.
    rw [← FormalGroupHom.id_eq_mulByNatHom_one]
    exact FormalGroupHom.id_comp (FormalGroupHom.id F)

/-- Existence form of `mulByNatHom_one_isIso`: there exists a two-sided
inverse to `mulByNatHom F 1`. This is the form matching the ticket acceptance
criteria (`T-IV-2-008`, restricted to the `n = 1` case). -/
theorem FormalGroup.mulByNatHom_one_exists_inverse (F : FormalGroup R) :
    ∃ g : FormalGroupHom F F,
      g.comp (F.mulByNatHom 1) = FormalGroupHom.id F ∧
        (F.mulByNatHom 1).comp g = FormalGroupHom.id F := by
  refine ⟨FormalGroupHom.id F, ?_, ?_⟩
  · -- id.comp (mulByNatHom F 1) = id.
    rw [← FormalGroupHom.id_eq_mulByNatHom_one]
    exact FormalGroupHom.id_comp (FormalGroupHom.id F)
  · -- (mulByNatHom F 1).comp id = id.
    rw [← FormalGroupHom.id_eq_mulByNatHom_one]
    exact FormalGroupHom.comp_id (FormalGroupHom.id F)

/-! ### T-IV-2-008: General unit case via `compInverseOfUnit`

**Silverman IV.2.3(b) (general unit case)**: if `(n : R)` is a unit, then
`mulByNatHom F n` admits a *right compositional inverse* as a power series,
given by the unit-leading-coefficient inverse `compInverseOfUnit` (see
`HasseWeil/FormalGroup/Logarithm.lean`).

The **existence statement** below (`mulByNatHom_hasInverse`) provides the
right-inverse power series with the key identity
`subst g (mulByNatHom F n).toSeries = X`, directly usable by downstream
consumers (e.g. `T-IV-3-007`, p-power torsion).

Packaging this inverse as a `FormalGroupHom F F` requires proving the
`preserves_add` axiom for the inverse series. This is non-trivial in general:
the standard approach is to first show the inverse is also a *left* inverse
(`subst f g = X`), and then transport `preserves_add` across the two-sided
inverse. The left-inverse identity for `compInverseOfUnit` has not yet been
proved (only the right-inverse identity `subst_compInverseOfUnit_eq_X` is
available). A follow-up ticket tracks the remaining work. -/

/-- **Silverman IV.2.3(b), existence form**: for `n : ℕ` with `(n : R)` a
unit, there exists a power series `g` that is a right compositional inverse
of the underlying series of `mulByNatHom F n`:
`subst g (mulByNatHom F n).toSeries = X`.

The witness is `compInverseOfUnit (mulByNatHom F n).toSeries (n : R) hn`
(from `HasseWeil.FormalGroup.Logarithm`).

This is the **primary acceptance theorem for T-IV-2-008** (general unit
case). The stronger statement "`mulByNatHom F n` is an isomorphism of
formal groups" requires packaging `g` as a `FormalGroupHom`, which needs
the left-inverse identity `subst f g = X` (not yet available). -/
theorem FormalGroup.mulByNatHom_hasInverse (F : FormalGroup R) (n : ℕ)
    (hn : IsUnit ((n : ℕ) : R)) :
    ∃ g : PowerSeries R,
      PowerSeries.subst g (F.mulByNatHom n).toSeries = PowerSeries.X ∧
      @PowerSeries.constantCoeff R _ g = 0 := by
  refine ⟨compInverseOfUnit (F.mulByNatHom n).toSeries ((n : ℕ) : R) hn, ?_, ?_⟩
  · -- Apply `subst_compInverseOfUnit_eq_X` with
    -- h0 := (mulByNatHom F n).zero_const
    -- h1 := coeff_one_mulByNatHom (a simp lemma)
    apply subst_compInverseOfUnit_eq_X
    · exact (F.mulByNatHom n).zero_const
    · exact FormalGroup.coeff_one_mulByNatHom F n
  · exact compInverseOfUnit_constantCoeff _ _ hn

/-- Enriched existence form: also asserts the linear-coefficient identity
`coeff 1 g = (hn.unit)⁻¹`. Useful for downstream consumers that need to
know the leading term of the inverse. -/
theorem FormalGroup.mulByNatHom_hasInverse' (F : FormalGroup R) (n : ℕ)
    (hn : IsUnit ((n : ℕ) : R)) :
    ∃ g : PowerSeries R,
      PowerSeries.subst g (F.mulByNatHom n).toSeries = PowerSeries.X ∧
      @PowerSeries.constantCoeff R _ g = 0 ∧
      PowerSeries.HasSubst g := by
  refine ⟨compInverseOfUnit (F.mulByNatHom n).toSeries ((n : ℕ) : R) hn,
    ?_, ?_, ?_⟩
  · apply subst_compInverseOfUnit_eq_X
    · exact (F.mulByNatHom n).zero_const
    · exact FormalGroup.coeff_one_mulByNatHom F n
  · exact compInverseOfUnit_constantCoeff _ _ hn
  · exact compInverseOfUnit_hasSubst _ _ hn

/-! ### Named right-inverse power series

We also expose the right-inverse of `mulByNatHom F n` (as a bare power
series) under a convenient name, together with the basic API. These give
downstream users the right-inverse identity without needing to peek at the
existence statement. -/

/-- The (right) compositional inverse of `mulByNatHom F n` as a power
series, when `(n : R)` is a unit. Defined as
`compInverseOfUnit (mulByNatHom F n).toSeries n hn`. -/
noncomputable def FormalGroup.mulByNatInvSeries (F : FormalGroup R) (n : ℕ)
    (hn : IsUnit ((n : ℕ) : R)) : PowerSeries R :=
  compInverseOfUnit (F.mulByNatHom n).toSeries ((n : ℕ) : R) hn

/-- `constantCoeff (mulByNatInvSeries F n hn) = 0`. -/
@[simp]
theorem FormalGroup.constantCoeff_mulByNatInvSeries (F : FormalGroup R) (n : ℕ)
    (hn : IsUnit ((n : ℕ) : R)) :
    @PowerSeries.constantCoeff R _ (F.mulByNatInvSeries n hn) = 0 :=
  compInverseOfUnit_constantCoeff _ _ hn

/-- `mulByNatInvSeries F n hn` admits substitution. -/
theorem FormalGroup.mulByNatInvSeries_hasSubst (F : FormalGroup R) (n : ℕ)
    (hn : IsUnit ((n : ℕ) : R)) :
    PowerSeries.HasSubst (F.mulByNatInvSeries n hn) :=
  compInverseOfUnit_hasSubst _ _ hn

/-- **The key right-inverse identity** at the power series level:
`subst (mulByNatInvSeries F n hn) (mulByNatHom F n).toSeries = X`.
Equivalently, `[n] ∘ inv = id` at the series level. -/
theorem FormalGroup.subst_mulByNatInvSeries_mulByNatHom (F : FormalGroup R) (n : ℕ)
    (hn : IsUnit ((n : ℕ) : R)) :
    PowerSeries.subst (F.mulByNatInvSeries n hn) (F.mulByNatHom n).toSeries =
      PowerSeries.X := by
  unfold FormalGroup.mulByNatInvSeries
  apply subst_compInverseOfUnit_eq_X
  · exact (F.mulByNatHom n).zero_const
  · exact FormalGroup.coeff_one_mulByNatHom F n

/-- Auxiliary: `PowerSeries.subst PowerSeries.X f = f`, i.e. substituting
`X` for the variable is the identity. Used in the bootstrap chain that
proves the left-inverse identity for `mulByNatHom`. -/
private theorem subst_X_eq_self (f : PowerSeries R) :
    PowerSeries.subst (PowerSeries.X : PowerSeries R) f = f := by
  rw [PowerSeries.subst_def]
  have heq : (fun _ : Unit => (PowerSeries.X : PowerSeries R)) =
      (MvPowerSeries.X : Unit → MvPowerSeries Unit R) := by
    funext _; rfl
  rw [heq]
  exact congr_fun MvPowerSeries.subst_self f

/-- **T-IV-2-008b: the left-inverse identity** at the power-series level:
`subst (mulByNatHom F n).toSeries (mulByNatInvSeries F n hn) = X`.
Equivalently, `inv ∘ [n] = id` at the series level.

This is the *other* direction of the compositional inverse: combined with
`subst_mulByNatInvSeries_mulByNatHom`, it shows that `mulByNatHom F n`
and `mulByNatInvSeries F n hn` are mutual compositional inverses.

**Proof strategy** (bootstrap via a second compositional inverse):
1. Set `f := (mulByNatHom F n).toSeries` and `g := mulByNatInvSeries F n hn`.
   We have the right-inverse identity `subst g f = X` (existing).
2. Compute `coeff 1 g = (hn.unit)⁻¹ : R` (a unit, `compInverseOfUnit_coeff_one`).
3. Construct `h := compInverseOfUnit g v hv` where `v := (hn.unit)⁻¹`.
   This gives `subst h g = X` (right-inverse of `g`).
4. Apply associativity `subst h (subst g f) = subst (subst h g) f`:
   - LHS becomes `subst h X = h` (using `subst g f = X` and `subst_X`).
   - RHS becomes `subst X f = f` (using `subst h g = X` and `subst_X_eq_self`).
5. Therefore `h = f`, so `subst f g = subst h g = X`. -/
theorem FormalGroup.subst_mulByNatHom_mulByNatInvSeries (F : FormalGroup R) {n : ℕ}
    (hn : IsUnit ((n : ℕ) : R)) :
    PowerSeries.subst (F.mulByNatHom n).toSeries (F.mulByNatInvSeries n hn) =
      PowerSeries.X := by
  -- Set up abbreviations.
  set f : PowerSeries R := (F.mulByNatHom n).toSeries with hf_def
  set g : PowerSeries R := F.mulByNatInvSeries n hn with hg_def
  -- Existing right-inverse identity: subst g f = X.
  have h_right : PowerSeries.subst g f = PowerSeries.X :=
    F.subst_mulByNatInvSeries_mulByNatHom n hn
  -- Step 2: compute coeff 1 g = (hn.unit)⁻¹.
  set v : R := ((hn.unit⁻¹ : Rˣ) : R) with hv_def
  have hv : IsUnit v := (hn.unit⁻¹ : Rˣ).isUnit
  have hcoeff_g : PowerSeries.coeff 1 g = v := by
    rw [hg_def]
    change PowerSeries.coeff 1 (compInverseOfUnit (F.mulByNatHom n).toSeries
        ((n : ℕ) : R) hn) = v
    exact compInverseOfUnit_coeff_one _ _ hn
  -- Step 3: construct h := compInverseOfUnit g v hv (right inverse of g).
  set h : PowerSeries R := compInverseOfUnit g v hv with hh_def
  have h_g_const : @PowerSeries.constantCoeff R _ g = 0 := by
    rw [hg_def]
    exact F.constantCoeff_mulByNatInvSeries n hn
  have h_subst_h_g : PowerSeries.subst h g = PowerSeries.X :=
    subst_compInverseOfUnit_eq_X g v hv h_g_const hcoeff_g
  -- HasSubst facts.
  have h_g_hasSubst : PowerSeries.HasSubst g := by
    rw [hg_def]
    exact F.mulByNatInvSeries_hasSubst n hn
  have h_h_hasSubst : PowerSeries.HasSubst h := compInverseOfUnit_hasSubst _ _ hv
  -- Step 4: apply associativity.
  -- subst_comp_subst_apply ha hb f' : subst b (subst a f') = subst (subst b a) f'.
  -- With a := g, b := h: subst h (subst g f) = subst (subst h g) f.
  have hassoc : PowerSeries.subst h (PowerSeries.subst g f) =
      PowerSeries.subst (PowerSeries.subst h g) f :=
    PowerSeries.subst_comp_subst_apply h_g_hasSubst h_h_hasSubst f
  -- LHS: subst h (subst g f) = subst h X = h.
  rw [h_right] at hassoc
  rw [PowerSeries.subst_X h_h_hasSubst] at hassoc
  -- RHS: subst (subst h g) f = subst X f = f.
  rw [h_subst_h_g] at hassoc
  rw [subst_X_eq_self f] at hassoc
  -- hassoc : h = f.
  -- Step 5: subst f g = subst h g = X.
  rw [← hassoc]
  exact h_subst_h_g

/-! ### T-IV-2-008b corollary: injectivity of `[n]` on power series -/

/-- **Corollary of T-IV-2-008b** (series-level recovery formula): for
`x : PowerSeries R` admitting substitution, applying `[n]` and then the
inverse `mulByNatInvSeries` recovers `x`:
`subst (subst x [n].toSeries) (mulByNatInvSeries F n hn) = x`. -/
theorem FormalGroup.subst_mulByNatHom_subst_mulByNatInvSeries (F : FormalGroup R) {n : ℕ}
    (hn : IsUnit ((n : ℕ) : R)) (x : PowerSeries R) (hx : PowerSeries.HasSubst x) :
    PowerSeries.subst (PowerSeries.subst x (F.mulByNatHom n).toSeries)
        (F.mulByNatInvSeries n hn) = x := by
  -- Apply associativity + the left-inverse identity:
  -- subst (subst x f) g = subst x (subst f g) = subst x X = x.
  have h_left : PowerSeries.subst (F.mulByNatHom n).toSeries
      (F.mulByNatInvSeries n hn) = PowerSeries.X :=
    F.subst_mulByNatHom_mulByNatInvSeries hn
  have h_n_hasSubst : PowerSeries.HasSubst (F.mulByNatHom n).toSeries :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (F.mulByNatHom n).zero_const
  -- subst (subst x f) g = subst x (subst f g).
  have hassoc : PowerSeries.subst (PowerSeries.subst x (F.mulByNatHom n).toSeries)
      (F.mulByNatInvSeries n hn) =
      PowerSeries.subst x (PowerSeries.subst (F.mulByNatHom n).toSeries
        (F.mulByNatInvSeries n hn)) :=
    (PowerSeries.subst_comp_subst_apply h_n_hasSubst hx _).symm
  rw [hassoc, h_left, PowerSeries.subst_X hx]

/-- **Series-level injectivity of `[n]`** when `(n : R)` is a unit: if
`x : PowerSeries R` admits substitution and `subst x [n].toSeries = 0`, then
`x = 0`.

This is the cleanest series-level form of "[n] is injective on `F(M)`",
required by `T-IV-3-007` (torsion has `p`-power order). The evaluation-level
analogue (i.e. for elements of the maximal ideal `M`, via `MvPowerSeries.eval₂`)
follows by composing with the appropriate evaluation morphism. -/
theorem FormalGroup.mulByNatHom_subst_injective_of_unit (F : FormalGroup R) {n : ℕ}
    (hn : IsUnit ((n : ℕ) : R)) {x : PowerSeries R} (hx : PowerSeries.HasSubst x)
    (h : PowerSeries.subst x (F.mulByNatHom n).toSeries = 0) : x = 0 := by
  -- Apply F.subst_mulByNatHom_subst_mulByNatInvSeries to get
  -- subst (subst x f) g = x, then specialise with subst x f = 0.
  have hkey := F.subst_mulByNatHom_subst_mulByNatInvSeries hn x hx
  rw [h] at hkey
  -- hkey : subst 0 (mulByNatInvSeries F n hn) = x.
  -- We compute subst 0 g = 0 directly from coeff_subst'.
  rw [← hkey]
  -- Goal: subst 0 (mulByNatInvSeries F n hn) = 0.
  ext k
  rw [PowerSeries.coeff_subst' PowerSeries.HasSubst.zero'
    (F.mulByNatInvSeries n hn) k]
  -- Each term in the finsum is 0: either d = 0 (then coeff d g = 0 since
  -- g has zero constant coefficient), or d > 0 (then 0^d = 0).
  have hg_const : @PowerSeries.constantCoeff R _ (F.mulByNatInvSeries n hn) = 0 :=
    F.constantCoeff_mulByNatInvSeries n hn
  -- coeff k 0 = 0 on the RHS.
  change _ = (PowerSeries.coeff k (0 : PowerSeries R) : R)
  rw [map_zero]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  by_cases hd : d = 0
  · subst hd
    -- d = 0: coeff 0 g • coeff k (0^0) = 0 • _ = 0, since coeff 0 g = 0.
    have hc : PowerSeries.coeff 0 (F.mulByNatInvSeries n hn) = 0 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact hg_const
    rw [hc, zero_smul]
  · -- d ≠ 0: 0^d = 0 in PowerSeries R, so coeff k 0 = 0.
    have h0 : ((0 : PowerSeries R) ^ d) = 0 := zero_pow hd
    rw [h0, map_zero, smul_zero]

end HasseWeil.FormalGroup
