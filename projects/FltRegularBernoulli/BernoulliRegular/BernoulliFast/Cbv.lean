/-
Copyright (c) 2026 Bernoulli-Regular project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bernoulli-Regular project contributors
-/
import BernoulliRegular.BernoulliFast.Correctness
import Mathlib.Data.List.Defs
import Lean.Elab.Tactic.Cbv

/-!
# `cbv`-optimized Bernoulli number evaluation

This module provides a proof-producing evaluator for concrete Bernoulli
numbers.  It uses a small fraction representation and `cbv` simprocs that
collapse ground fraction operations and literal-list traversals in one step.

The main public definitions are:

* `BernoulliRegular.BernoulliFast.Cbv.Frac` — the integer/natural fraction
  representation used by the evaluator;
* `BernoulliRegular.BernoulliFast.Cbv.toRat` — interpretation of a fraction as
  a rational number;
* `BernoulliRegular.BernoulliFast.Cbv.bernoulliFrac` — the concrete evaluator.
-/

namespace BernoulliRegular.BernoulliFast.Cbv

/-- Integer numerator and natural denominator, used only for fast ground
normalization by `cbv`. -/
abbrev Frac := Int × Nat

/-- Interpret a `Frac` as a rational number. -/
def toRat (f : Frac) : ℚ :=
  mkRat f.1 f.2

private def valid (f : Frac) : Prop :=
  f.2 ≠ 0

/-! ## Fraction primitives -/

private def simplify : Frac → Frac
  | (_, 0) => (0, 1)
  | (p, q) =>
    let g := Nat.gcd p.natAbs q
    (p / (g : Int), q / g)

private def negF (f : Frac) : Frac := (-f.1, f.2)

private def addF : Frac → Frac → Frac
  | (p1, q1), (p2, q2) =>
    let g := Nat.gcd q1 q2
    let lcm := q1 / g * q2
    simplify (p1 * ((q2 / g) : Int) + p2 * ((q1 / g) : Int), lcm)

private def mulF : Frac → Frac → Frac
  | (p1, q1), (p2, q2) =>
    simplify (p1 * p2, q1 * q2)

private def mulN (f : Frac) (c : Nat) : Frac :=
  let (p, q) := f
  let g := Nat.gcd c q
  simplify (p * ((c / g) : Int), q / g)

private def mulZ (f : Frac) (z : Int) : Frac :=
  let (p, q) := f
  simplify (p * z, q)

private def divN (f : Frac) (d : Nat) : Frac :=
  let (p, q) := f
  let g := Nat.gcd p.natAbs d
  simplify (p / (g : Int), q * (d / g))

/-! ## Rational soundness of the fraction primitives -/

private theorem toRat_simplify {f : Frac} (hf : f.2 ≠ 0) :
    toRat (simplify f) = toRat f := by
  rcases f with ⟨p, q⟩
  dsimp at hf
  simp only [toRat]
  rw [show
      simplify (p, q) =
        (p / ((Nat.gcd p.natAbs q : Nat) : Int), q / Nat.gcd p.natAbs q) by
    simp [simplify]]
  let g := Nat.gcd p.natAbs q
  have hg0 : g ≠ 0 := Nat.gcd_ne_zero_right hf
  have hpdiv : (g : Int) ∣ p :=
    Int.ofNat_dvd_left.2 (Nat.gcd_dvd_left p.natAbs q)
  have hp : (g : Int) * (p / (g : Int)) = p :=
    Int.mul_ediv_cancel' hpdiv
  have hq : g * (q / g) = q := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_cancel (Nat.gcd_dvd_right p.natAbs q)
  have h := Rat.mkRat_mul_left (n := p / (g : Int)) (d := q / g) hg0
  rw [hp, hq] at h
  exact h.symm

private theorem simplify_den_ne_zero {f : Frac} (hf : f.2 ≠ 0) :
    (simplify f).2 ≠ 0 := by
  rcases f with ⟨p, q⟩
  dsimp at hf
  rw [show
      (simplify (p, q)).2 = q / Nat.gcd p.natAbs q by
    simp [simplify]]
  have hqPos : 0 < q := Nat.pos_of_ne_zero hf
  exact (Nat.div_pos
    (Nat.gcd_le_right _ hqPos)
    (Nat.gcd_pos_of_pos_right _ hqPos)).ne'

private theorem toRat_negF (f : Frac) : toRat (negF f) = -toRat f := by
  rcases f with ⟨p, q⟩
  simp [toRat, negF, Rat.neg_mkRat]

private theorem negF_den_ne_zero {f : Frac} (hf : valid f) : valid (negF f) := by
  rcases f with ⟨p, q⟩
  simpa [valid, negF] using hf

private theorem addF_den_ne_zero {f₁ f₂ : Frac} (h₁ : f₁.2 ≠ 0) (h₂ : f₂.2 ≠ 0) :
    (addF f₁ f₂).2 ≠ 0 := by
  rcases f₁ with ⟨p₁, q₁⟩
  rcases f₂ with ⟨p₂, q₂⟩
  dsimp at h₁ h₂
  simp only [addF]
  let g := Nat.gcd q₁ q₂
  have hq₁g : q₁ / g ≠ 0 :=
    (Nat.div_pos (Nat.gcd_le_left q₂ (Nat.pos_of_ne_zero h₁))
      (Nat.gcd_pos_of_pos_left q₂ (Nat.pos_of_ne_zero h₁))).ne'
  have hlcm : q₁ / g * q₂ ≠ 0 := Nat.mul_ne_zero hq₁g h₂
  have hsimp :
      (simplify
        (p₁ * ((q₂ / g) : Int) + p₂ * ((q₁ / g) : Int), q₁ / g * q₂)).2 =
        (q₁ / g * q₂) /
          Nat.gcd (p₁ * ((q₂ / g) : Int) + p₂ * ((q₁ / g) : Int)).natAbs
            (q₁ / g * q₂) := by
    simp [simplify]
  rw [hsimp]
  have hlcmPos : 0 < q₁ / g * q₂ := Nat.pos_of_ne_zero hlcm
  exact (Nat.div_pos
    (Nat.gcd_le_right _ hlcmPos)
    (Nat.gcd_pos_of_pos_right _ hlcmPos)).ne'

private theorem toRat_addF {f₁ f₂ : Frac} (h₁ : f₁.2 ≠ 0) (h₂ : f₂.2 ≠ 0) :
    toRat (addF f₁ f₂) = toRat f₁ + toRat f₂ := by
  rcases f₁ with ⟨p₁, q₁⟩
  rcases f₂ with ⟨p₂, q₂⟩
  dsimp at h₁ h₂
  simp only [addF]
  let g := Nat.gcd q₁ q₂
  have hg0 : g ≠ 0 := Nat.gcd_ne_zero_left h₁
  have hq₁g : q₁ / g ≠ 0 :=
    (Nat.div_pos (Nat.gcd_le_left q₂ (Nat.pos_of_ne_zero h₁))
      (Nat.gcd_pos_of_pos_left q₂ (Nat.pos_of_ne_zero h₁))).ne'
  have hlcm : q₁ / g * q₂ ≠ 0 := Nat.mul_ne_zero hq₁g h₂
  change
    toRat
        (simplify
          (p₁ * ((q₂ / g) : Int) + p₂ * ((q₁ / g) : Int), q₁ / g * q₂)) =
      toRat (p₁, q₁) + toRat (p₂, q₂)
  rw [toRat_simplify
    (f := (p₁ * ((q₂ / g) : Int) + p₂ * ((q₁ / g) : Int), q₁ / g * q₂)) hlcm]
  simp only [toRat]
  rw [Rat.mkRat_add_mkRat _ _ h₁ h₂]
  have hnum :
      (p₁ * ((q₂ / g) : Int) + p₂ * ((q₁ / g) : Int)) * (g : Int) =
        p₁ * (q₂ : Int) + p₂ * (q₁ : Int) := by
    have hq₂ : ((q₂ : Int) / (g : Int)) * (g : Int) = (q₂ : Int) :=
      Int.ediv_mul_cancel (Int.ofNat_dvd.2 (Nat.gcd_dvd_right q₁ q₂))
    have hq₁ : ((q₁ : Int) / (g : Int)) * (g : Int) = (q₁ : Int) :=
      Int.ediv_mul_cancel (Int.ofNat_dvd.2 (Nat.gcd_dvd_left q₁ q₂))
    calc
      (p₁ * ((q₂ / g) : Int) + p₂ * ((q₁ / g) : Int)) * (g : Int)
          = p₁ * (((q₂ : Int) / (g : Int)) * (g : Int)) +
              p₂ * (((q₁ : Int) / (g : Int)) * (g : Int)) := by
            ring_nf
      _ = p₁ * (q₂ : Int) + p₂ * (q₁ : Int) := by rw [hq₂, hq₁]
  have hden : (q₁ / g * q₂) * g = q₁ * q₂ := by
    rw [Nat.mul_assoc, Nat.mul_comm q₂ g, ← Nat.mul_assoc]
    rw [Nat.div_mul_cancel (Nat.gcd_dvd_left q₁ q₂)]
  have h := Rat.mkRat_mul_right
    (n := p₁ * ((q₂ / g) : Int) + p₂ * ((q₁ / g) : Int))
    (d := q₁ / g * q₂) hg0
  rw [hnum, hden] at h
  exact h.symm

private theorem mulF_den_ne_zero {f₁ f₂ : Frac} (h₁ : f₁.2 ≠ 0) (h₂ : f₂.2 ≠ 0) :
    (mulF f₁ f₂).2 ≠ 0 := by
  rcases f₁ with ⟨p₁, q₁⟩
  rcases f₂ with ⟨p₂, q₂⟩
  exact simplify_den_ne_zero (f := (p₁ * p₂, q₁ * q₂)) (Nat.mul_ne_zero h₁ h₂)

private theorem toRat_mulF {f₁ f₂ : Frac} (h₁ : f₁.2 ≠ 0) (h₂ : f₂.2 ≠ 0) :
    toRat (mulF f₁ f₂) = toRat f₁ * toRat f₂ := by
  rcases f₁ with ⟨p₁, q₁⟩
  rcases f₂ with ⟨p₂, q₂⟩
  dsimp at h₁ h₂
  simp only [mulF]
  rw [toRat_simplify (f := (p₁ * p₂, q₁ * q₂)) (Nat.mul_ne_zero h₁ h₂)]
  simp [toRat, Rat.mkRat_mul_mkRat]

private theorem mulN_den_ne_zero {f : Frac} (hf : f.2 ≠ 0) (c : Nat) :
    (mulN f c).2 ≠ 0 := by
  rcases f with ⟨p, q⟩
  dsimp at hf
  simp only [mulN]
  let g := Nat.gcd c q
  have hqg : q / g ≠ 0 :=
    (Nat.div_pos (Nat.gcd_le_right c (Nat.pos_of_ne_zero hf))
      (Nat.gcd_pos_of_pos_right c (Nat.pos_of_ne_zero hf))).ne'
  have hsimp : (simplify (p * ((c / g) : Int), q / g)).2 =
      (q / g) / Nat.gcd (p * ((c / g) : Int)).natAbs (q / g) := by
    simp [simplify]
  rw [hsimp]
  have hqgPos : 0 < q / g := Nat.pos_of_ne_zero hqg
  exact (Nat.div_pos
    (Nat.gcd_le_right _ hqgPos)
    (Nat.gcd_pos_of_pos_right _ hqgPos)).ne'

private theorem toRat_mulN {f : Frac} (hf : f.2 ≠ 0) (c : Nat) :
    toRat (mulN f c) = toRat f * (c : ℚ) := by
  rcases f with ⟨p, q⟩
  dsimp at hf
  simp only [mulN]
  let g := Nat.gcd c q
  have hg0 : g ≠ 0 := Nat.gcd_ne_zero_right hf
  have hqg : q / g ≠ 0 :=
    (Nat.div_pos (Nat.gcd_le_right c (Nat.pos_of_ne_zero hf))
      (Nat.gcd_pos_of_pos_right c (Nat.pos_of_ne_zero hf))).ne'
  change toRat (simplify (p * ((c / g) : Int), q / g)) = toRat (p, q) * (c : ℚ)
  rw [toRat_simplify (f := (p * ((c / g) : Int), q / g)) hqg]
  simp only [toRat]
  rw [show (c : ℚ) = mkRat (c : Int) 1 by
    rw [Rat.mkRat_eq_div]
    norm_num]
  rw [Rat.mkRat_mul_mkRat]
  simp only [Nat.mul_one]
  have hnum : p * ((c / g) : Int) * (g : Int) = p * (c : Int) := by
    have hc : ((c : Int) / (g : Int)) * (g : Int) = (c : Int) :=
      Int.ediv_mul_cancel (Int.ofNat_dvd.2 (Nat.gcd_dvd_left c q))
    calc
      p * ((c / g) : Int) * (g : Int)
          = p * (((c : Int) / (g : Int)) * (g : Int)) := by ring_nf
      _ = p * (c : Int) := by rw [hc]
  have hden : (q / g) * g = q := by
    rw [Nat.div_mul_cancel (Nat.gcd_dvd_right c q)]
  have h := Rat.mkRat_mul_right (n := p * ((c / g) : Int)) (d := q / g) hg0
  rw [hnum, hden] at h
  exact h.symm

private theorem mulZ_den_ne_zero {f : Frac} (hf : f.2 ≠ 0) (z : Int) :
    (mulZ f z).2 ≠ 0 := by
  rcases f with ⟨p, q⟩
  exact simplify_den_ne_zero (f := (p * z, q)) hf

private theorem toRat_mulZ {f : Frac} (hf : f.2 ≠ 0) (z : Int) :
    toRat (mulZ f z) = toRat f * (z : ℚ) := by
  rcases f with ⟨p, q⟩
  dsimp at hf
  simp only [mulZ]
  rw [toRat_simplify (f := (p * z, q)) hf]
  simp only [toRat]
  rw [show (z : ℚ) = mkRat z 1 by
    rw [Rat.mkRat_eq_div]
    norm_num]
  rw [Rat.mkRat_mul_mkRat]
  simp

private theorem divN_den_ne_zero {f : Frac} (hf : f.2 ≠ 0) {d : Nat} (hd : d ≠ 0) :
    (divN f d).2 ≠ 0 := by
  rcases f with ⟨p, q⟩
  dsimp at hf
  simp only [divN]
  let g := Nat.gcd p.natAbs d
  have hdg : d / g ≠ 0 :=
    (Nat.div_pos (Nat.gcd_le_right p.natAbs (Nat.pos_of_ne_zero hd))
      (Nat.gcd_pos_of_pos_right p.natAbs (Nat.pos_of_ne_zero hd))).ne'
  have hden : q * (d / g) ≠ 0 := Nat.mul_ne_zero hf hdg
  have hsimp : (simplify (p / (g : Int), q * (d / g))).2 =
      (q * (d / g)) / Nat.gcd (p / (g : Int)).natAbs (q * (d / g)) := by
    simp [simplify]
  rw [hsimp]
  have hdenPos : 0 < q * (d / g) := Nat.pos_of_ne_zero hden
  exact (Nat.div_pos
    (Nat.gcd_le_right _ hdenPos)
    (Nat.gcd_pos_of_pos_right _ hdenPos)).ne'

private theorem toRat_divN {f : Frac} (hf : f.2 ≠ 0) {d : Nat} (hd : d ≠ 0) :
    toRat (divN f d) = toRat f / (d : ℚ) := by
  rcases f with ⟨p, q⟩
  dsimp at hf
  simp only [divN]
  let g := Nat.gcd p.natAbs d
  have hg0 : g ≠ 0 := Nat.gcd_ne_zero_right hd
  have hdg : d / g ≠ 0 :=
    (Nat.div_pos (Nat.gcd_le_right p.natAbs (Nat.pos_of_ne_zero hd))
      (Nat.gcd_pos_of_pos_right p.natAbs (Nat.pos_of_ne_zero hd))).ne'
  have hden : q * (d / g) ≠ 0 := Nat.mul_ne_zero hf hdg
  change toRat (simplify (p / (g : Int), q * (d / g))) = toRat (p, q) / (d : ℚ)
  rw [toRat_simplify (f := (p / (g : Int), q * (d / g))) hden]
  simp only [toRat]
  have hdiv : mkRat p q / (d : ℚ) = mkRat p (q * d) := by
    rw [Rat.mkRat_eq_div, Rat.mkRat_eq_div]
    have hq : (q : ℚ) ≠ 0 := by exact_mod_cast hf
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
    field_simp [hq, hdq]
    norm_num [Nat.cast_mul]
    ring
  rw [hdiv]
  have hnum : (g : Int) * (p / (g : Int)) = p :=
    Int.mul_ediv_cancel' (Int.ofNat_dvd_left.2 (Nat.gcd_dvd_left p.natAbs d))
  have hden' : g * (q * (d / g)) = q * d := by
    have hdNat : d / g * g = d := Nat.div_mul_cancel (Nat.gcd_dvd_right p.natAbs d)
    calc
      g * (q * (d / g)) = q * (d / g * g) := by ring
      _ = q * d := by rw [hdNat]
  have h := Rat.mkRat_mul_left (n := p / (g : Int)) (d := q * (d / g)) hg0
  rw [hnum, hden'] at h
  exact h.symm

/-! ## Simprocs for `Frac` and literal `List` traversal

Without these, every `Frac` op unfolds through a long typeclass chain
(`HMul.hMul → instHMul → Mul.mul → Int.instMul → Int.mul → ...`) and
`simplify` rebuilds a `Prod` via pattern matching, and every list traversal
walks a cons-by-cons equation unfolding.  The simprocs below extract ground
values, compute the result in meta code, and emit a single-step `Eq.refl`. -/

open Lean Meta Lean.Meta.Tactic.Cbv

namespace CbvBernoulli

/-- Extract an `Int` literal in any canonical form `cbv` might produce:
`OfNat.ofNat Int k`, `Neg.neg (OfNat.ofNat Int k)`, `Int.ofNat k`, or
`Int.negSucc k`. -/
def getIntValue? (e : Expr) : OptionT Id Int :=
  match_expr e with
  | Int.ofNat n => do
      let some n := Sym.getNatValue? n | failure
      return (n : Int)
  | Int.negSucc n => do
      let some n := Sym.getNatValue? n | failure
      return Int.negSucc n
  | _ => Sym.getIntValue? e

def getFracValue? (e : Expr) : OptionT Id Frac := do
  let_expr Prod.mk _ _ p q := e | failure
  let p ← getIntValue? p
  let q ← Sym.getNatValue? q
  return (p, q)

def mkFracExpr (f : Frac) : Expr :=
  mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Int) (mkConst ``Nat)
    (toExpr f.1) (toExpr f.2)

def mkListLit (α : Expr) (u : Level) (xs : Array Expr) : Expr :=
  let nil := mkApp (mkConst ``List.nil [u]) α
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [u]) α x acc) nil

end CbvBernoulli

open CbvBernoulli

cbv_simproc cbv_eval simpSimplify (simplify _) := fun e => do
  let_expr simplify a := e | return .rfl
  let some f := getFracValue? a | return .rfl
  let result ← Sym.share (mkFracExpr (simplify f))
  return .step result (← Sym.mkEqRefl result)

cbv_simproc cbv_eval simpNegF (negF _) := fun e => do
  let_expr negF a := e | return .rfl
  let some f := getFracValue? a | return .rfl
  let result ← Sym.share (mkFracExpr (negF f))
  return .step result (← Sym.mkEqRefl result)

cbv_simproc cbv_eval simpAddF (addF _ _) := fun e => do
  let_expr addF a b := e | return .rfl
  let some f₁ := getFracValue? a | return .rfl
  let some f₂ := getFracValue? b | return .rfl
  let result ← Sym.share (mkFracExpr (addF f₁ f₂))
  return .step result (← Sym.mkEqRefl result)

cbv_simproc cbv_eval simpMulF (mulF _ _) := fun e => do
  let_expr mulF a b := e | return .rfl
  let some f₁ := getFracValue? a | return .rfl
  let some f₂ := getFracValue? b | return .rfl
  let result ← Sym.share (mkFracExpr (mulF f₁ f₂))
  return .step result (← Sym.mkEqRefl result)

cbv_simproc cbv_eval simpMulN (mulN _ _) := fun e => do
  let_expr mulN a c := e | return .rfl
  let some f := getFracValue? a | return .rfl
  let some c := Sym.getNatValue? c | return .rfl
  let result ← Sym.share (mkFracExpr (mulN f c))
  return .step result (← Sym.mkEqRefl result)

cbv_simproc cbv_eval simpMulZ (mulZ _ _) := fun e => do
  let_expr mulZ a z := e | return .rfl
  let some f := getFracValue? a | return .rfl
  let some z := CbvBernoulli.getIntValue? z | return .rfl
  let result ← Sym.share (mkFracExpr (mulZ f z))
  return .step result (← Sym.mkEqRefl result)

cbv_simproc cbv_eval simpDivN (divN _ _) := fun e => do
  let_expr divN a d := e | return .rfl
  let some f := getFracValue? a | return .rfl
  let some d := Sym.getNatValue? d | return .rfl
  let result ← Sym.share (mkFracExpr (divN f d))
  return .step result (← Sym.mkEqRefl result)

/-- `xs ++ ys` for literal lists becomes a single literal list. -/
cbv_simproc cbv_eval simpListAppend (@HAppend.hAppend (List _) (List _) (List _) _ _ _) :=
    fun e => do
  let_expr HAppend.hAppend α _ _ _ a b := e | return .rfl
  let_expr List β := α | return .rfl
  let some aElems := getListLitElems a | return .rfl
  let some bElems := getListLitElems b | return .rfl
  let .succ u := (← Sym.getLevel β) | return .rfl
  let result ← Sym.share (mkListLit β u (aElems ++ bElems))
  return .step result (← Sym.mkEqRefl result)

cbv_simproc cbv_eval simpListLength (List.length _) := fun e => do
  let_expr List.length _ a := e | return .rfl
  let some elems := getListLitElems a | return .rfl
  let result ← Sym.share (toExpr elems.size)
  return .step result (← Sym.mkEqRefl result)

cbv_simproc cbv_eval simpListTail (List.tail _) := fun e => do
  let_expr List.tail α a := e | return .rfl
  let some elems := getListLitElems a | return .rfl
  let .succ u := (← Sym.getLevel α) | return .rfl
  let tail := if elems.size = 0 then elems else elems[1:].toArray
  let result ← Sym.share (mkListLit α u tail)
  return .step result (← Sym.mkEqRefl result)

cbv_simproc cbv_eval simpListZipWith (List.zipWith _ _ _) := fun e => do
  let_expr List.zipWith _ _ γ f a b := e | return .rfl
  let some aElems := getListLitElems a | return .rfl
  let some bElems := getListLitElems b | return .rfl
  let k := min aElems.size bElems.size
  let out ← (Array.range k).mapM fun i =>
    Sym.share (mkApp2 f aElems[i]! bElems[i]!)
  let .succ u := (← Sym.getLevel γ) | return .rfl
  let result ← Sym.share (mkListLit γ u out)
  return .step result (← Sym.mkEqRefl result)

cbv_simproc cbv_eval simpListZip (List.zip _ _) := fun e => do
  let_expr List.zip α β a b := e | return .rfl
  let some aElems := getListLitElems a | return .rfl
  let some bElems := getListLitElems b | return .rfl
  let k := min aElems.size bElems.size
  let .succ uα := (← Sym.getLevel α) | return .rfl
  let .succ uβ := (← Sym.getLevel β) | return .rfl
  let out ← (Array.range k).mapM fun i =>
    Sym.share (mkApp4 (mkConst ``Prod.mk [uα, uβ]) α β aElems[i]! bElems[i]!)
  let prodT := mkApp2 (mkConst ``Prod [uα, uβ]) α β
  let u := mkLevelMax uα uβ
  let result ← Sym.share (mkListLit prodT u out)
  return .step result (← Sym.mkEqRefl result)

cbv_simproc cbv_eval simpListMap (List.map _ _) := fun e => do
  let_expr List.map _ β f a := e | return .rfl
  let some aElems := getListLitElems a | return .rfl
  let out ← aElems.mapM fun x => Sym.share (mkApp f x)
  let .succ u := (← Sym.getLevel β) | return .rfl
  let result ← Sym.share (mkListLit β u out)
  return .step result (← Sym.mkEqRefl result)

/-! ## Certified mirror of `BernoulliFast.bernoulliCompute` -/

private def binomSumFrac.loop (m : Nat) : List Frac → Nat → Frac → Frac → Frac
  | [], _, _, acc => acc
  | b :: rest, k, c, acc =>
    binomSumFrac.loop m rest (k + 1)
      (divN (mulZ c ((m : Int) - (k : Int))) (k + 1))
      (addF acc (mulF c b))

private def binomSumFrac (bs : List Frac) (m : Nat) : Frac :=
  binomSumFrac.loop m bs 0 (1, 1) (0, 1)

/-- The same recurrence as `BernoulliFast.bernoulliList`, but using the
`Frac` primitives so concrete proofs can normalize by `cbv`. -/
def bernoulliComputeFracList : Nat → List Frac
  | 0 => [(1, 1)]
  | n + 1 =>
    let prev := bernoulliComputeFracList n
    let s := binomSumFrac prev (n + 2)
    prev ++ [negF (divN s (n + 2))]

/-- `Frac` version of `BernoulliFast.bernoulliCompute`, with the same
recurrence and a rational-correctness theorem below. -/
def bernoulliComputeFrac (n : Nat) : Frac :=
  (bernoulliComputeFracList n).getLast!

private theorem binomSumFrac_loop_valid (m : Nat) (bs : List Frac) (k : Nat) (c acc : Frac)
    (hbs : bs.Forall valid) (hc : valid c) (hacc : valid acc) :
    valid (binomSumFrac.loop m bs k c acc) := by
  induction bs generalizing k c acc with
  | nil =>
      simpa [binomSumFrac.loop] using hacc
  | cons b rest ih =>
      have hbs' : valid b ∧ rest.Forall valid := by
        simpa [List.Forall] using hbs
      simp only [binomSumFrac.loop]
      exact ih (k + 1)
        (divN (mulZ c ((m : Int) - (k : Int))) (k + 1))
        (addF acc (mulF c b)) hbs'.2
        (divN_den_ne_zero (mulZ_den_ne_zero hc _) (Nat.succ_ne_zero k))
        (addF_den_ne_zero hacc (mulF_den_ne_zero hc hbs'.1))

private theorem binomSumFrac_loop_toRat (m : Nat) (bs : List Frac) (k : Nat) (c acc : Frac)
    (hbs : bs.Forall valid) (hc : valid c) (hacc : valid acc) :
    toRat (binomSumFrac.loop m bs k c acc) =
      BernoulliRegular.BernoulliFast.binomSum.loop m (bs.map toRat) k (toRat c) (toRat acc) := by
  induction bs generalizing k c acc with
  | nil =>
      simp [binomSumFrac.loop, BernoulliRegular.BernoulliFast.binomSum.loop]
  | cons b rest ih =>
      have hbs' : valid b ∧ rest.Forall valid := by
        simpa [List.Forall] using hbs
      simp only [binomSumFrac.loop, List.map_cons,
        BernoulliRegular.BernoulliFast.binomSum.loop]
      rw [ih (k + 1)
        (divN (mulZ c ((m : Int) - (k : Int))) (k + 1))
        (addF acc (mulF c b)) hbs'.2
        (divN_den_ne_zero (mulZ_den_ne_zero hc _) (Nat.succ_ne_zero k))
        (addF_den_ne_zero hacc (mulF_den_ne_zero hc hbs'.1))]
      rw [toRat_divN (mulZ_den_ne_zero hc _) (Nat.succ_ne_zero k),
        toRat_mulZ hc, toRat_addF hacc (mulF_den_ne_zero hc hbs'.1),
        toRat_mulF hc hbs'.1]
      norm_num [Int.cast_sub, Nat.cast_add, sub_eq_add_neg]

private theorem binomSumFrac_valid (bs : List Frac) (m : Nat) (hbs : bs.Forall valid) :
    valid (binomSumFrac bs m) :=
  binomSumFrac_loop_valid m bs 0 (1, 1) (0, 1) hbs (by simp [valid]) (by simp [valid])

private theorem binomSumFrac_toRat (bs : List Frac) (m : Nat) (hbs : bs.Forall valid) :
    toRat (binomSumFrac bs m) =
      BernoulliRegular.BernoulliFast.binomSum (bs.map toRat) m :=
  binomSumFrac_loop_toRat m bs 0 (1, 1) (0, 1) hbs (by simp [valid]) (by simp [valid])

private theorem bernoulliComputeFracList_valid (n : Nat) :
    (bernoulliComputeFracList n).Forall valid := by
  induction n with
  | zero =>
      simp [bernoulliComputeFracList, List.Forall, valid]
  | succ n ih =>
      have hs : valid (binomSumFrac (bernoulliComputeFracList n) (n + 2)) :=
        binomSumFrac_valid _ _ ih
      have hnew : valid
          (negF (divN (binomSumFrac (bernoulliComputeFracList n) (n + 2)) (n + 2))) :=
        negF_den_ne_zero (divN_den_ne_zero hs (Nat.succ_ne_zero (n + 1)))
      simp [bernoulliComputeFracList, List.Forall, ih, hnew]

private theorem bernoulliComputeFracList_toRat (n : Nat) :
    (bernoulliComputeFracList n).map toRat =
      BernoulliRegular.BernoulliFast.bernoulliList n := by
  induction n with
  | zero =>
      simp [bernoulliComputeFracList, BernoulliRegular.BernoulliFast.bernoulliList,
        toRat, Rat.mkRat_eq_div]
  | succ n ih =>
      have hvalid := bernoulliComputeFracList_valid n
      have hs :
          toRat (binomSumFrac (bernoulliComputeFracList n) (n + 2)) =
            BernoulliRegular.BernoulliFast.binomSum
              ((bernoulliComputeFracList n).map toRat) (n + 2) :=
        binomSumFrac_toRat _ _ hvalid
      have hsValid : valid (binomSumFrac (bernoulliComputeFracList n) (n + 2)) :=
        binomSumFrac_valid _ _ hvalid
      simp only [bernoulliComputeFracList, BernoulliRegular.BernoulliFast.bernoulliList,
        List.map_append, List.map_cons, List.map_nil, ih]
      rw [toRat_negF, toRat_divN hsValid (Nat.succ_ne_zero (n + 1)), hs, ih]
      norm_num [Nat.cast_add, add_comm, add_left_comm, add_assoc]
      ring

private theorem getLast!_map_toRat (l : List Frac) :
    (l.map toRat).getLast! = toRat l.getLast! := by
  cases l with
  | nil =>
      norm_num [List.getLast!, toRat, Rat.mkRat_eq_div]
      rfl
  | cons a as =>
      induction as generalizing a with
      | nil =>
          simp [List.getLast!]
      | cons b bs ih =>
          simpa [List.getLast!] using ih b

/-- The mirrored `Frac` recurrence agrees with the existing certified
`BernoulliFast.bernoulliCompute`. -/
theorem bernoulliComputeFrac_toRat_eq_bernoulliCompute (n : Nat) :
    toRat (bernoulliComputeFrac n) =
      BernoulliRegular.BernoulliFast.bernoulliCompute n := by
  have h := congrArg List.getLast! (bernoulliComputeFracList_toRat n)
  rw [getLast!_map_toRat] at h
  simpa [bernoulliComputeFrac, BernoulliRegular.BernoulliFast.bernoulliCompute] using h

/-- The mirrored `Frac` recurrence agrees with Mathlib's Bernoulli number. -/
theorem bernoulliComputeFrac_toRat_eq_bernoulli (n : Nat) :
    toRat (bernoulliComputeFrac n) = bernoulli n := by
  rw [bernoulliComputeFrac_toRat_eq_bernoulliCompute,
    BernoulliRegular.BernoulliFast.bernoulliCompute_eq]

/-- Default certified `Frac` Bernoulli table. -/
abbrev bernoulliFracList := bernoulliComputeFracList

/-- Default certified `Frac` Bernoulli number. -/
abbrev bernoulliFrac := bernoulliComputeFrac

/-- The default certified `Frac` evaluator agrees with the existing certified
`BernoulliFast.bernoulliCompute`. -/
theorem bernoulliFrac_toRat_eq_bernoulliCompute (n : Nat) :
    toRat (bernoulliFrac n) =
      BernoulliRegular.BernoulliFast.bernoulliCompute n :=
  bernoulliComputeFrac_toRat_eq_bernoulliCompute n

/-- The default certified `Frac` evaluator agrees with Mathlib's Bernoulli
number. -/
theorem bernoulliFrac_toRat_eq_bernoulli (n : Nat) :
    toRat (bernoulliFrac n) = bernoulli n :=
  bernoulliComputeFrac_toRat_eq_bernoulli n

/-! ## Pascal-row recurrence -/

/-- Next Pascal row: `[C(n,0), C(n,1), ..., C(n,n)]` to
`[C(n+1,0), C(n+1,1), ..., C(n+1,n+1)]`. -/
private def nextPascalRow (row : List Nat) : List Nat :=
  let mid := (row.zip row.tail).map (fun (a, b) => a + b)
  [1] ++ mid ++ [1]

/-- Given known Bernoulli numbers and the matching Pascal row, compute the
next Bernoulli number.  `bs.zip row` truncates to `bs.length` pairs; the row
is intentionally one coefficient longer. -/
private def nextBernoulli (bs : List Frac) (row : List Nat) : Frac :=
  let k := bs.length
  let weightedSum := (bs.zip row).foldl (fun acc (bj, cj) => addF acc (mulN bj cj)) (0, 1)
  negF (divN weightedSum (k + 1))

/-- Carry the Pascal row as a second accumulator. -/
private def go : Nat → List Frac → List Nat → List Frac
  | 0, bs, _ => bs
  | n + 1, bs, row => go n (bs ++ [nextBernoulli bs row]) (nextPascalRow row)

/-- Pascal-row table `[B₀, ..., Bₙ]`, represented as `Frac`s. -/
def bernoulliPascalFracList (n : Nat) : List Frac :=
  go n [(1, 1)] [1, 2, 1]

/-- Pascal-row `Frac` evaluator from the original experiment.

This is faster for large concrete `cbv` evaluations than the certified mirror
above, but the theorem-level Mathlib bridge is currently provided for
`bernoulliFrac`. -/
def bernoulliPascalFrac (n : Nat) : Frac :=
  (bernoulliPascalFracList n).getLast!

example : bernoulliPascalFrac 9 = (0, 1) := by cbv
example : bernoulliPascalFrac 18 = (43867, 798) := by cbv
example : bernoulliPascalFrac 20 = (-174611, 330) := by cbv

set_option maxRecDepth 1_000_000_000 in
set_option maxHeartbeats 1_000_000_000 in
-- This example is a stress-test for the intended B100 proof-producing evaluation use case.
set_option cbv.maxSteps 10_000_000 in
example :
    bernoulliPascalFrac 100 =
      (-94598037819122125295227433069493721872702841533066936133385696204311395415197247711,
        33330) := by
  cbv

end BernoulliRegular.BernoulliFast.Cbv
