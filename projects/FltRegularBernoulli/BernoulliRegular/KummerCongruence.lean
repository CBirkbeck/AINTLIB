module

public import BernoulliRegular.KummerCongruence.VonStaudtClausen
public import BernoulliRegular.KummerCongruence.Voronoi
public import BernoulliRegular.KummerCongruence.Kummer
public import BernoulliRegular.KummerCongruence.Bridge

/-!
# Kummer congruences (umbrella)

This file re-exports the four submodules:

- `BernoulliRegular.KummerCongruence.VonStaudtClausen`: vSC + Step 2 + Adams
- `BernoulliRegular.KummerCongruence.Voronoi`: Cohen Prop 9.5.20
- `BernoulliRegular.KummerCongruence.Kummer`: T011 (classical Kummer congruence)
- `BernoulliRegular.KummerCongruence.Bridge`: T012 (main bridge) + T013 (boundary case)

Key theorems:
- `bernoulliGen_teichmuller_pow_sModEq_div` (T012)
- `bernoulli_div_sModEq_of_modEq` (T011)
- `voronoi_congruence_mod_p` (Cohen Prop 9.5.20)

All three depend only on the standard Lean axioms
`propext, Classical.choice, Quot.sound`.
-/
