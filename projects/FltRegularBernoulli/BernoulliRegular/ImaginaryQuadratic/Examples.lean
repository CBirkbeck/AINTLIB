module

public import BernoulliRegular.ImaginaryQuadratic.CN05.Proof

@[expose] public section

noncomputable section

open Complex NumberField

namespace BernoulliRegular

/-! ### Proof of concept: the chain works for `p = 3`

We directly verify that for `p = 3`, the integer character sum is `-1 < 0`,
giving `rootNumber (legendreDirichlet 3) = 1` unconditionally.

For `p = 3`:
  `(0/3) · 0 + (1/3) · 1 + (2/3) · 2 = 0 · 0 + 1 · 1 + (-1) · 2 = -1 < 0`. -/

/-- Numerical fact: `∑_{a : ZMod 3} (a/3) · a = -1` as an integer. -/
theorem integer_sum_three :
    ∑ a : ZMod 3, (quadraticChar (ZMod 3) a : ℤ) * (a.val : ℤ) = -1 := by
  decide

/-- Real-valued version: `∑_{a : ZMod 3} (a/3) · a = -1 < 0`. -/
theorem integer_sum_real_neg_three :
    (∑ a : ZMod 3, ((quadraticChar (ZMod 3) a : ℤ) : ℝ) * (a.val : ℝ)) < 0 := by
  have h : ∑ a : ZMod 3, ((quadraticChar (ZMod 3) a : ℤ) : ℝ) * (a.val : ℝ) =
      ((∑ a : ZMod 3, (quadraticChar (ZMod 3) a : ℤ) * (a.val : ℤ) : ℤ) : ℝ) := by
    push_cast
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [h, integer_sum_three]
  norm_num

/-- **Unconditional for p = 3**: `rootNumber (legendreDirichlet 3) = 1`. -/
theorem rootNumber_legendreDirichlet_three_eq_one :
    DirichletCharacter.rootNumber (legendreDirichlet 3) = 1 :=
  rootNumber_eq_one_of_sum_neg 3 (by decide) integer_sum_real_neg_three

/-- **Unconditional for p = 3**: `τ(η) = I · √3`. -/
theorem gaussSum_legendreDirichlet_three_eq :
    gaussSum (legendreDirichlet 3) (ZMod.stdAddChar : AddChar (ZMod 3) ℂ) =
      Complex.I * ((3 : ℂ) ^ (1 / 2 : ℂ)) :=
  gaussSum_eq_I_mul_sqrt_of_sum_neg 3 (by decide) integer_sum_real_neg_three

/-- **Unconditional for p = 3**: the clean Dedekind FE for `ℚ(ζ_3)`. -/
theorem completedDedekindZetaCyclotomic_three_cleanFE (s : ℂ) :
    completedDedekindZetaCyclotomic 3 (1 - s) =
      (3 : ℂ) ^ ((1 : ℕ) * (s - 1 / 2 : ℂ)) *
        completedDedekindZetaCyclotomic 3 s :=
  completedDedekindZetaCyclotomic_cleanFE_of_sum_neg 3 (by decide)
    integer_sum_real_neg_three s

/-! ### Proof of concept: the chain works for `p = 7` -/

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- Numerical fact for p = 7: `∑_{a : ZMod 7} (a/7) · a = -7`. -/
theorem integer_sum_seven :
    ∑ a : ZMod 7, (quadraticChar (ZMod 7) a : ℤ) * (a.val : ℤ) = -7 := by
  decide

/-- **Unconditional for p = 7**: `τ(η) = I · √7`. -/
theorem gaussSum_legendreDirichlet_seven_eq :
    gaussSum (legendreDirichlet 7) (ZMod.stdAddChar : AddChar (ZMod 7) ℂ) =
      Complex.I * ((7 : ℂ) ^ (1 / 2 : ℂ)) := by
  apply gaussSum_eq_I_mul_sqrt_of_int_sum_neg 7 (by decide)
  rw [integer_sum_seven]; decide

/-! ### Proof of concept: the chain works for `p = 11` -/

instance : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- Numerical fact for p = 11: `∑_{a : ZMod 11} (a/11) · a = -11`. -/
theorem integer_sum_eleven :
    ∑ a : ZMod 11, (quadraticChar (ZMod 11) a : ℤ) * (a.val : ℤ) = -11 := by
  decide

/-- **Unconditional for p = 11**: `τ(η) = I · √11`. -/
theorem gaussSum_legendreDirichlet_eleven_eq :
    gaussSum (legendreDirichlet 11) (ZMod.stdAddChar : AddChar (ZMod 11) ℂ) =
      Complex.I * ((11 : ℂ) ^ (1 / 2 : ℂ)) := by
  apply gaussSum_eq_I_mul_sqrt_of_int_sum_neg 11 (by decide)
  rw [integer_sum_eleven]; decide

/-! ### Proof of concept: the chain works for `p = 19` -/

instance : Fact (Nat.Prime 19) := ⟨by decide⟩

/-- Numerical fact for p = 19: `∑_{a : ZMod 19} (a/19) · a = -19`. -/
theorem integer_sum_nineteen :
    ∑ a : ZMod 19, (quadraticChar (ZMod 19) a : ℤ) * (a.val : ℤ) = -19 := by
  decide

/-- **Unconditional for p = 19**: `τ(η) = I · √19`. -/
theorem gaussSum_legendreDirichlet_nineteen_eq :
    gaussSum (legendreDirichlet 19) (ZMod.stdAddChar : AddChar (ZMod 19) ℂ) =
      Complex.I * ((19 : ℂ) ^ (1 / 2 : ℂ)) := by
  apply gaussSum_eq_I_mul_sqrt_of_int_sum_neg 19 (by decide)
  rw [integer_sum_nineteen]; decide

/-! ### Proof of concept: the chain works for `p = 23` -/

instance : Fact (Nat.Prime 23) := ⟨by decide⟩

/-- Numerical fact for p = 23: `∑_{a : ZMod 23} (a/23) · a = -69`.

Here `h(-23) = 3` (class number of `ℚ(√-23)`), so sum = -23 · 3 = -69. -/
theorem integer_sum_twentythree :
    ∑ a : ZMod 23, (quadraticChar (ZMod 23) a : ℤ) * (a.val : ℤ) = -69 := by
  decide

/-- **Unconditional for p = 23**: `τ(η) = I · √23`. -/
theorem gaussSum_legendreDirichlet_twentythree_eq :
    gaussSum (legendreDirichlet 23) (ZMod.stdAddChar : AddChar (ZMod 23) ℂ) =
      Complex.I * ((23 : ℂ) ^ (1 / 2 : ℂ)) := by
  apply gaussSum_eq_I_mul_sqrt_of_int_sum_neg 23 (by decide)
  rw [integer_sum_twentythree]; decide

/-! ### Proof of concept: the chain works for `p = 31` -/

instance : Fact (Nat.Prime 31) := ⟨by decide⟩

/-- Numerical fact for p = 31: `∑_{a : ZMod 31} (a/31) · a = -93`.

Here `h(-31) = 3`, so sum = -31 · 3 = -93. -/
theorem integer_sum_thirtyone :
    ∑ a : ZMod 31, (quadraticChar (ZMod 31) a : ℤ) * (a.val : ℤ) = -93 := by
  decide

/-- **Unconditional for p = 31**: `τ(η) = I · √31`. -/
theorem gaussSum_legendreDirichlet_thirtyone_eq :
    gaussSum (legendreDirichlet 31) (ZMod.stdAddChar : AddChar (ZMod 31) ℂ) =
      Complex.I * ((31 : ℂ) ^ (1 / 2 : ℂ)) := by
  apply gaussSum_eq_I_mul_sqrt_of_int_sum_neg 31 (by decide)
  rw [integer_sum_thirtyone]; decide

/-! ### Proof of concept: the chain works for `p = 43` -/

instance : Fact (Nat.Prime 43) := ⟨by decide⟩

/-- Numerical fact for p = 43: `∑_{a : ZMod 43} (a/43) · a = -43`.

Here `h(-43) = 1`, so sum = -43 · 1 = -43. -/
theorem integer_sum_fortythree :
    ∑ a : ZMod 43, (quadraticChar (ZMod 43) a : ℤ) * (a.val : ℤ) = -43 := by
  decide

/-- **Unconditional for p = 43**: `τ(η) = I · √43`. -/
theorem gaussSum_legendreDirichlet_fortythree_eq :
    gaussSum (legendreDirichlet 43) (ZMod.stdAddChar : AddChar (ZMod 43) ℂ) =
      Complex.I * ((43 : ℂ) ^ (1 / 2 : ℂ)) := by
  apply gaussSum_eq_I_mul_sqrt_of_int_sum_neg 43 (by decide)
  rw [integer_sum_fortythree]; decide

/-! ### Proof of concept: the chain works for `p = 47` -/

instance : Fact (Nat.Prime 47) := ⟨by decide⟩

set_option maxRecDepth 4000 in
/-- Numerical fact for p = 47: `∑_{a : ZMod 47} (a/47) · a = -235`.

Here `h(-47) = 5`, so sum = -47 · 5 = -235. -/
theorem integer_sum_fortyseven :
    ∑ a : ZMod 47, (quadraticChar (ZMod 47) a : ℤ) * (a.val : ℤ) = -235 := by
  decide

/-- **Unconditional for p = 47**: `τ(η) = I · √47`. -/
theorem gaussSum_legendreDirichlet_fortyseven_eq :
    gaussSum (legendreDirichlet 47) (ZMod.stdAddChar : AddChar (ZMod 47) ℂ) =
      Complex.I * ((47 : ℂ) ^ (1 / 2 : ℂ)) := by
  apply gaussSum_eq_I_mul_sqrt_of_int_sum_neg 47 (by decide)
  rw [integer_sum_fortyseven]; decide

/-! ### Proof of concept: the chain works for `p = 59` -/

instance : Fact (Nat.Prime 59) := ⟨by decide⟩

set_option maxRecDepth 4000 in
/-- Numerical fact for p = 59: `∑_{a : ZMod 59} (a/59) · a = -177`.

Here `h(-59) = 3`, so sum = -59 · 3 = -177. -/
theorem integer_sum_fiftynine :
    ∑ a : ZMod 59, (quadraticChar (ZMod 59) a : ℤ) * (a.val : ℤ) = -177 := by
  decide

/-- **Unconditional for p = 59**: `τ(η) = I · √59`. -/
theorem gaussSum_legendreDirichlet_fiftynine_eq :
    gaussSum (legendreDirichlet 59) (ZMod.stdAddChar : AddChar (ZMod 59) ℂ) =
      Complex.I * ((59 : ℂ) ^ (1 / 2 : ℂ)) := by
  apply gaussSum_eq_I_mul_sqrt_of_int_sum_neg 59 (by decide)
  rw [integer_sum_fiftynine]; decide

/-! ### Proof of concept: the chain works for `p = 67` -/

instance : Fact (Nat.Prime 67) := ⟨by decide⟩

set_option maxRecDepth 4000 in
/-- Numerical fact for p = 67: `∑_{a : ZMod 67} (a/67) · a = -67`.

Here `h(-67) = 1`, so sum = -67 · 1 = -67. -/
theorem integer_sum_sixtyseven :
    ∑ a : ZMod 67, (quadraticChar (ZMod 67) a : ℤ) * (a.val : ℤ) = -67 := by
  decide

/-- **Unconditional for p = 67**: `τ(η) = I · √67`. -/
theorem gaussSum_legendreDirichlet_sixtyseven_eq :
    gaussSum (legendreDirichlet 67) (ZMod.stdAddChar : AddChar (ZMod 67) ℂ) =
      Complex.I * ((67 : ℂ) ^ (1 / 2 : ℂ)) := by
  apply gaussSum_eq_I_mul_sqrt_of_int_sum_neg 67 (by decide)
  rw [integer_sum_sixtyseven]; decide

/-! ### Proof of concept: the chain works for `p = 71` -/

instance : Fact (Nat.Prime 71) := ⟨by decide⟩

set_option maxRecDepth 4000 in
/-- Numerical fact for p = 71: `∑_{a : ZMod 71} (a/71) · a = -497`.

Here `h(-71) = 7`, so sum = -71 · 7 = -497. -/
theorem integer_sum_seventyone :
    ∑ a : ZMod 71, (quadraticChar (ZMod 71) a : ℤ) * (a.val : ℤ) = -497 := by
  decide

/-- **Unconditional for p = 71**: `τ(η) = I · √71`. -/
theorem gaussSum_legendreDirichlet_seventyone_eq :
    gaussSum (legendreDirichlet 71) (ZMod.stdAddChar : AddChar (ZMod 71) ℂ) =
      Complex.I * ((71 : ℂ) ^ (1 / 2 : ℂ)) := by
  apply gaussSum_eq_I_mul_sqrt_of_int_sum_neg 71 (by decide)
  rw [integer_sum_seventyone]; decide

/-! ### Proof of concept: the chain works for `p = 79` -/

instance : Fact (Nat.Prime 79) := ⟨by decide⟩

set_option maxRecDepth 4000 in
/-- Numerical fact for p = 79: `∑_{a : ZMod 79} (a/79) · a = -395`.

Here `h(-79) = 5`, so sum = -79 · 5 = -395. -/
theorem integer_sum_seventynine :
    ∑ a : ZMod 79, (quadraticChar (ZMod 79) a : ℤ) * (a.val : ℤ) = -395 := by
  decide

/-- **Unconditional for p = 79**: `τ(η) = I · √79`. -/
theorem gaussSum_legendreDirichlet_seventynine_eq :
    gaussSum (legendreDirichlet 79) (ZMod.stdAddChar : AddChar (ZMod 79) ℂ) =
      Complex.I * ((79 : ℂ) ^ (1 / 2 : ℂ)) := by
  apply gaussSum_eq_I_mul_sqrt_of_int_sum_neg 79 (by decide)
  rw [integer_sum_seventynine]; decide

/-! ### Proof of concept: the chain works for `p = 83` -/

instance : Fact (Nat.Prime 83) := ⟨by decide⟩

set_option maxRecDepth 4000 in
/-- Numerical fact for p = 83: `∑_{a : ZMod 83} (a/83) · a = -249`.

Here `h(-83) = 3`, so sum = -83 · 3 = -249. -/
theorem integer_sum_eightythree :
    ∑ a : ZMod 83, (quadraticChar (ZMod 83) a : ℤ) * (a.val : ℤ) = -249 := by
  decide

/-- **Unconditional for p = 83**: `τ(η) = I · √83`. -/
theorem gaussSum_legendreDirichlet_eightythree_eq :
    gaussSum (legendreDirichlet 83) (ZMod.stdAddChar : AddChar (ZMod 83) ℂ) =
      Complex.I * ((83 : ℂ) ^ (1 / 2 : ℂ)) := by
  apply gaussSum_eq_I_mul_sqrt_of_int_sum_neg 83 (by decide)
  rw [integer_sum_eightythree]; decide

/-! ### Proof of concept: the chain works for `p = 103` -/

instance : Fact (Nat.Prime 103) := ⟨by decide⟩

set_option maxRecDepth 8000 in
/-- Numerical fact for p = 103: `∑_{a : ZMod 103} (a/103) · a = -515`.

Here `h(-103) = 5`, so sum = -103 · 5 = -515. -/
theorem integer_sum_onehundredthree :
    ∑ a : ZMod 103, (quadraticChar (ZMod 103) a : ℤ) * (a.val : ℤ) = -515 := by
  decide

/-- **Unconditional for p = 103**: `τ(η) = I · √103`. -/
theorem gaussSum_legendreDirichlet_onehundredthree_eq :
    gaussSum (legendreDirichlet 103) (ZMod.stdAddChar : AddChar (ZMod 103) ℂ) =
      Complex.I * ((103 : ℂ) ^ (1 / 2 : ℂ)) := by
  apply gaussSum_eq_I_mul_sqrt_of_int_sum_neg 103 (by decide)
  rw [integer_sum_onehundredthree]; decide

/-! ### Proof of concept: the chain works for `p = 107` -/

instance : Fact (Nat.Prime 107) := ⟨by decide⟩

set_option maxRecDepth 8000 in
/-- Numerical fact for p = 107: `∑_{a : ZMod 107} (a/107) · a = -321`.

Here `h(-107) = 3`, so sum = -107 · 3 = -321. -/
theorem integer_sum_onehundredseven :
    ∑ a : ZMod 107, (quadraticChar (ZMod 107) a : ℤ) * (a.val : ℤ) = -321 := by
  decide

/-- **Unconditional for p = 107**: `τ(η) = I · √107`. -/
theorem gaussSum_legendreDirichlet_onehundredseven_eq :
    gaussSum (legendreDirichlet 107) (ZMod.stdAddChar : AddChar (ZMod 107) ℂ) =
      Complex.I * ((107 : ℂ) ^ (1 / 2 : ℂ)) := by
  apply gaussSum_eq_I_mul_sqrt_of_int_sum_neg 107 (by decide)
  rw [integer_sum_onehundredseven]; decide

/-! ### Proof of concept: the chain works for `p = 127` -/

instance : Fact (Nat.Prime 127) := ⟨by decide⟩

set_option maxRecDepth 8000 in
/-- Numerical fact for p = 127: `∑_{a : ZMod 127} (a/127) · a = -635`.

Here `h(-127) = 5`, so sum = -127 · 5 = -635. -/
theorem integer_sum_onehundredtwentyseven :
    ∑ a : ZMod 127, (quadraticChar (ZMod 127) a : ℤ) * (a.val : ℤ) = -635 := by
  decide

/-- **Unconditional for p = 127**: `τ(η) = I · √127`. -/
theorem gaussSum_legendreDirichlet_onehundredtwentyseven_eq :
    gaussSum (legendreDirichlet 127) (ZMod.stdAddChar : AddChar (ZMod 127) ℂ) =
      Complex.I * ((127 : ℂ) ^ (1 / 2 : ℂ)) := by
  apply gaussSum_eq_I_mul_sqrt_of_int_sum_neg 127 (by decide)
  rw [integer_sum_onehundredtwentyseven]; decide

/-! ### Proof of concept: the chain works for `p = 131` -/

instance : Fact (Nat.Prime 131) := ⟨by decide⟩

set_option maxRecDepth 8000 in
/-- Numerical fact for p = 131: `∑_{a : ZMod 131} (a/131) · a = -655`.

Here `h(-131) = 5`, so sum = -131 · 5 = -655. -/
theorem integer_sum_onehundredthirtyone :
    ∑ a : ZMod 131, (quadraticChar (ZMod 131) a : ℤ) * (a.val : ℤ) = -655 := by
  decide

/-- **Unconditional for p = 131**: `τ(η) = I · √131`. -/
theorem gaussSum_legendreDirichlet_onehundredthirtyone_eq :
    gaussSum (legendreDirichlet 131) (ZMod.stdAddChar : AddChar (ZMod 131) ℂ) =
      Complex.I * ((131 : ℂ) ^ (1 / 2 : ℂ)) := by
  apply gaussSum_eq_I_mul_sqrt_of_int_sum_neg 131 (by decide)
  rw [integer_sum_onehundredthirtyone]; decide

/-! ### Proof of concept: the chain works for `p = 139` -/

instance : Fact (Nat.Prime 139) := ⟨by decide⟩

set_option maxRecDepth 8000 in
/-- Numerical fact for p = 139: `∑_{a : ZMod 139} (a/139) · a = -417`.

Here `h(-139) = 3`, so sum = -139 · 3 = -417. -/
theorem integer_sum_onehundredthirtynine :
    ∑ a : ZMod 139, (quadraticChar (ZMod 139) a : ℤ) * (a.val : ℤ) = -417 := by
  decide

/-- **Unconditional for p = 139**: `τ(η) = I · √139`. -/
theorem gaussSum_legendreDirichlet_onehundredthirtynine_eq :
    gaussSum (legendreDirichlet 139) (ZMod.stdAddChar : AddChar (ZMod 139) ℂ) =
      Complex.I * ((139 : ℂ) ^ (1 / 2 : ℂ)) := by
  apply gaussSum_eq_I_mul_sqrt_of_int_sum_neg 139 (by decide)
  rw [integer_sum_onehundredthirtynine]; decide

/-! ### Proof of concept: the chain works for `p = 151` -/

instance : Fact (Nat.Prime 151) := ⟨by decide⟩

set_option maxRecDepth 8000 in
/-- Numerical fact for p = 151: `∑_{a : ZMod 151} (a/151) · a = -1057`.

Here `h(-151) = 7`, so sum = -151 · 7 = -1057. -/
theorem integer_sum_onehundredfiftyone :
    ∑ a : ZMod 151, (quadraticChar (ZMod 151) a : ℤ) * (a.val : ℤ) = -1057 := by
  decide

/-- **Unconditional for p = 151**: `τ(η) = I · √151`. -/
theorem gaussSum_legendreDirichlet_onehundredfiftyone_eq :
    gaussSum (legendreDirichlet 151) (ZMod.stdAddChar : AddChar (ZMod 151) ℂ) =
      Complex.I * ((151 : ℂ) ^ (1 / 2 : ℂ)) := by
  apply gaussSum_eq_I_mul_sqrt_of_int_sum_neg 151 (by decide)
  rw [integer_sum_onehundredfiftyone]; decide

/-! ### Proof of concept: the chain works for `p = 163` (Heegner prime) -/

set_option maxRecDepth 4000 in
instance : Fact (Nat.Prime 163) := ⟨by decide⟩

set_option maxRecDepth 8000 in
/-- Numerical fact for p = 163: `∑_{a : ZMod 163} (a/163) · a = -163`.

Here `h(-163) = 1` (the largest imaginary quadratic class number 1, Heegner),
so sum = -163 · 1 = -163. -/
theorem integer_sum_onehundredsixtythree :
    ∑ a : ZMod 163, (quadraticChar (ZMod 163) a : ℤ) * (a.val : ℤ) = -163 := by
  decide

/-- **Unconditional for p = 163** (Heegner prime): `τ(η) = I · √163`. -/
theorem gaussSum_legendreDirichlet_onehundredsixtythree_eq :
    gaussSum (legendreDirichlet 163) (ZMod.stdAddChar : AddChar (ZMod 163) ℂ) =
      Complex.I * ((163 : ℂ) ^ (1 / 2 : ℂ)) := by
  apply gaussSum_eq_I_mul_sqrt_of_int_sum_neg 163 (by decide)
  rw [integer_sum_onehundredsixtythree]; decide

end BernoulliRegular
