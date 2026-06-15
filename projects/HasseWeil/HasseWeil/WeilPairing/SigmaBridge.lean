import HasseWeil.WeilPairing.Pullback

/-!
# Route 2A — the σ-bridge computation (Silverman III.6.1(b))

`σ(f*((Q)) − f*((O))) = (#ker f) · P₀` for any `P₀` with `f P₀ = Q`. This is the geometric heart of
the dual: `σ` of the pullback divisor of `(Q) − (O)` is `[deg_s f] P₀`, which for a separable `f`
(`deg_s = deg`) is `f̂(Q)`. Pure group theory over the kernel coset — the bridge the separable
adjoint (Silverman III.8.2) consumes once linked to the genuine dual.
-/

namespace HasseWeil.WeilPairing

set_option linter.unusedSectionVars false

open WeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F} [W.IsElliptic]

/-- Reindexing the fibre sum over the kernel coset: `Σ_{fP=Q} P = Σ_{T∈ker} (P₀ + T)`. -/
theorem fiber_sum_eq_ker_sum (f : W.Point →+ W.Point) (h : Finite f.ker) {P₀ Q : W.Point}
    (hP₀ : f P₀ = Q) :
    letI : Fintype {P : W.Point // f P = Q} := @Fintype.ofFinite _ (fiber_finite f h Q)
    letI : Fintype f.ker := @Fintype.ofFinite _ h
    (∑ P : {P : W.Point // f P = Q}, P.val) = ∑ T : f.ker, (P₀ + (T : W.Point)) := by
  letI : Fintype {P : W.Point // f P = Q} := @Fintype.ofFinite _ (fiber_finite f h Q)
  letI : Fintype f.ker := @Fintype.ofFinite _ h
  refine Fintype.sum_equiv (fiberEquivKer f hP₀) (fun P => P.val)
    (fun T => P₀ + (T : W.Point)) (fun P => ?_)
  simp only [fiberEquivKer, Equiv.coe_fn_mk]
  abel

/-- **The σ-bridge (Silverman III.6.1(b)):** `σ(f*((Q)) − f*((O))) = (#ker f) · P₀` for `f P₀ = Q`.
For separable `f` (`#ker f = deg f`), the right side is `[deg f] P₀ = f̂(Q)`. -/
theorem sigma_pullbackDiv_sub (f : W.Point →+ W.Point) (h : Finite f.ker) {P₀ Q : W.Point}
    (hP₀ : f P₀ = Q) :
    Curves.projectiveDivisorSum W (pullbackDiv f h Q) -
        Curves.projectiveDivisorSum W (pullbackDiv f h 0) = Nat.card f.ker • P₀ := by
  letI : Fintype f.ker := @Fintype.ofFinite _ h
  have hQ := projectiveDivisorSum_pullbackDiv f h Q
  have hO := projectiveDivisorSum_pullbackDiv f h 0
  rw [hQ, hO, fiber_sum_eq_ker_sum f h hP₀,
    fiber_sum_eq_ker_sum f h (by simp : f (0 : W.Point) = 0)]
  simp only [zero_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card]
  abel

end HasseWeil.WeilPairing
