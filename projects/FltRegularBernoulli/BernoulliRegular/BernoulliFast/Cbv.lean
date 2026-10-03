/-
Copyright (c) 2026 Bernoulli-Regular project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bernoulli-Regular project contributors
-/
module

public import BernoulliRegular.BernoulliFast.Cbv.Data
public meta import BernoulliRegular.BernoulliFast.Cbv.Data
import all BernoulliRegular.BernoulliFast.Cbv.Data
public meta import Lean.Meta.Sym.LitValues
public meta import Lean.Meta.Sym.InferType
public meta import Lean.Meta.Tactic.Cbv.Util
public import Mathlib.Data.List.Defs
public import Lean.Elab.Tactic.Cbv

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

set_option backward.privateInPublic true

@[expose] public section

namespace BernoulliRegular.BernoulliFast.Cbv

section Simprocs

public meta section

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
  xs.foldr (fun x acc ↦ mkApp3 (mkConst ``List.cons [u]) α x acc) nil

end CbvBernoulli

open CbvBernoulli

cbv_simproc cbv_eval simpSimplify (simplify _) := fun e ↦ do
  let_expr simplify a := e | return .rfl
  let some f := getFracValue? a | return .rfl
  let result ← Sym.share (mkFracExpr (simplify f))
  return .step result (← Sym.mkEqRefl result)

cbv_simproc cbv_eval simpNegF (negF _) := fun e ↦ do
  let_expr negF a := e | return .rfl
  let some f := getFracValue? a | return .rfl
  let result ← Sym.share (mkFracExpr (negF f))
  return .step result (← Sym.mkEqRefl result)

cbv_simproc cbv_eval simpAddF (addF _ _) := fun e ↦ do
  let_expr addF a b := e | return .rfl
  let some f₁ := getFracValue? a | return .rfl
  let some f₂ := getFracValue? b | return .rfl
  let result ← Sym.share (mkFracExpr (addF f₁ f₂))
  return .step result (← Sym.mkEqRefl result)

cbv_simproc cbv_eval simpMulF (mulF _ _) := fun e ↦ do
  let_expr mulF a b := e | return .rfl
  let some f₁ := getFracValue? a | return .rfl
  let some f₂ := getFracValue? b | return .rfl
  let result ← Sym.share (mkFracExpr (mulF f₁ f₂))
  return .step result (← Sym.mkEqRefl result)

cbv_simproc cbv_eval simpMulN (mulN _ _) := fun e ↦ do
  let_expr mulN a c := e | return .rfl
  let some f := getFracValue? a | return .rfl
  let some c := Sym.getNatValue? c | return .rfl
  let result ← Sym.share (mkFracExpr (mulN f c))
  return .step result (← Sym.mkEqRefl result)

cbv_simproc cbv_eval simpMulZ (mulZ _ _) := fun e ↦ do
  let_expr mulZ a z := e | return .rfl
  let some f := getFracValue? a | return .rfl
  let some z := CbvBernoulli.getIntValue? z | return .rfl
  let result ← Sym.share (mkFracExpr (mulZ f z))
  return .step result (← Sym.mkEqRefl result)

cbv_simproc cbv_eval simpDivN (divN _ _) := fun e ↦ do
  let_expr divN a d := e | return .rfl
  let some f := getFracValue? a | return .rfl
  let some d := Sym.getNatValue? d | return .rfl
  let result ← Sym.share (mkFracExpr (divN f d))
  return .step result (← Sym.mkEqRefl result)

/-- `xs ++ ys` for literal lists becomes a single literal list. -/
cbv_simproc cbv_eval simpListAppend (@HAppend.hAppend (List _) (List _) (List _) _ _ _) :=
    fun e ↦ do
  let_expr HAppend.hAppend α _ _ _ a b := e | return .rfl
  let_expr List β := α | return .rfl
  let some aElems := getListLitElems a | return .rfl
  let some bElems := getListLitElems b | return .rfl
  let .succ u := (← Sym.getLevel β) | return .rfl
  let result ← Sym.share (mkListLit β u (aElems ++ bElems))
  return .step result (← Sym.mkEqRefl result)

cbv_simproc cbv_eval simpListLength (List.length _) := fun e ↦ do
  let_expr List.length _ a := e | return .rfl
  let some elems := getListLitElems a | return .rfl
  let result ← Sym.share (toExpr elems.size)
  return .step result (← Sym.mkEqRefl result)

cbv_simproc cbv_eval simpListTail (List.tail _) := fun e ↦ do
  let_expr List.tail α a := e | return .rfl
  let some elems := getListLitElems a | return .rfl
  let .succ u := (← Sym.getLevel α) | return .rfl
  let tail := if elems.size = 0 then elems else elems[1:].toArray
  let result ← Sym.share (mkListLit α u tail)
  return .step result (← Sym.mkEqRefl result)

cbv_simproc cbv_eval simpListZipWith (List.zipWith _ _ _) := fun e ↦ do
  let_expr List.zipWith _ _ γ f a b := e | return .rfl
  let some aElems := getListLitElems a | return .rfl
  let some bElems := getListLitElems b | return .rfl
  let k := min aElems.size bElems.size
  let out ← (Array.range k).mapM fun i ↦
    Sym.share (mkApp2 f aElems[i]! bElems[i]!)
  let .succ u := (← Sym.getLevel γ) | return .rfl
  let result ← Sym.share (mkListLit γ u out)
  return .step result (← Sym.mkEqRefl result)

cbv_simproc cbv_eval simpListZip (List.zip _ _) := fun e ↦ do
  let_expr List.zip α β a b := e | return .rfl
  let some aElems := getListLitElems a | return .rfl
  let some bElems := getListLitElems b | return .rfl
  let k := min aElems.size bElems.size
  let .succ uα := (← Sym.getLevel α) | return .rfl
  let .succ uβ := (← Sym.getLevel β) | return .rfl
  let out ← (Array.range k).mapM fun i ↦
    Sym.share (mkApp4 (mkConst ``Prod.mk [uα, uβ]) α β aElems[i]! bElems[i]!)
  let prodT := mkApp2 (mkConst ``Prod [uα, uβ]) α β
  let u := mkLevelMax uα uβ
  let result ← Sym.share (mkListLit prodT u out)
  return .step result (← Sym.mkEqRefl result)

cbv_simproc cbv_eval simpListMap (List.map _ _) := fun e ↦ do
  let_expr List.map _ β f a := e | return .rfl
  let some aElems := getListLitElems a | return .rfl
  let out ← aElems.mapM fun x ↦ Sym.share (mkApp f x)
  let .succ u := (← Sym.getLevel β) | return .rfl
  let result ← Sym.share (mkListLit β u out)
  return .step result (← Sym.mkEqRefl result)

end

end Simprocs

example : bernoulliPascalFrac 9 = (0, 1) := by cbv
example : bernoulliPascalFrac 18 = (43867, 798) := by cbv
example : bernoulliPascalFrac 20 = (-174611, 330) := by cbv

set_option maxRecDepth 1_000_000_000 in
-- This example is a stress-test for the intended B100 proof-producing evaluation use case.
set_option cbv.maxSteps 10_000_000 in
example :
    bernoulliPascalFrac 100 =
      (-94598037819122125295227433069493721872702841533066936133385696204311395415197247711,
        33330) := by
  cbv

end BernoulliRegular.BernoulliFast.Cbv
