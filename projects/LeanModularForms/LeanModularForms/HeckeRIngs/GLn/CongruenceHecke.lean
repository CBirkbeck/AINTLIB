/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GLn.CongruenceHecke.Surjectivity

/-!
# Hecke Ring for Congruence Subgroups (Shimura §3.3)

Defines the Hecke pair `(Γ₀(N), Δ₀(N))` for congruence subgroups and establishes
the surjection `R(Γ, Δ) →+* R(Γ₀(N), Δ₀(N))` (Shimura Theorem 3.35).

This allows us to derive the multiplication table for any congruence subgroup
from the level-1 table (our Shimura 3.24 results) by applying the surjection
and computing its kernel (`T(p,p) ↦ 0` for `p | N`).

This file is the umbrella module of the `CongruenceHecke` development. The
content is split across the following modules (imported transitively here so
that downstream files may continue to `import …CongruenceHecke`):

* `CongruenceHecke.Foundation` — the Hecke pair `(Γ₀(N), Δ₀(N))` and the
  foundational double-coset lemmas (Shimura 3.28–3.29).
* `CongruenceHecke.Props` — the coset map and Propositions 3.30–3.33,
  including `T_bad_mul`.
* `CongruenceHecke.AtkinLehner` — the Atkin–Lehner anti-involution and the
  `CommRing` structure on `𝕋 (Γ₀(N)) ℤ`.
* `CongruenceHecke.Presentation` — the polynomial presentation `π`, the target
  ring hom `ψ`, and the factorization machinery.
* `CongruenceHecke.DegreeCombinatorics` — Chinese-remainder degree
  multiplicativity for `Γ₀(N)` double cosets.
* `CongruenceHecke.Surjectivity` — Shimura Theorem 3.35.

## Main definitions

* `Gamma0_pair` — the Hecke pair `(Γ₀(N), Δ₀(N))`

## Main results

* `shimura_thm_3_35` — `R(Γ, Δ) →+* R(Γ₀(N), Δ₀(N))` (Shimura Thm 3.35)

## Consequences for the multiplication table

By applying the surjection to our existing `T_sum_mul`, `T_sum_ppow_recurrence`,
etc., we get the level-N versions automatically. The key simplification: since
`T(p,p) ↦ 0` for `p | N`, the prime-power recurrence becomes

  For p ∤ N:  T'(p^{k+1}) = T'(p)T'(p^k) - p·T'(p,p)·T'(p^{k-1})  (same as level 1)
  For p | N:  T'(p^k) = T'(p)^k                                    (simplified)

and the general formula (3.3.6) becomes

  T'(m)T'(n) = Σ_{d|(m,n), (d,N)=1} d · T'(d,d) · T'(mn/d²).

The condition `(d,N) = 1` arises because `T'(d,d) = 0` when `d` has a factor dividing N.

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.3
-/
