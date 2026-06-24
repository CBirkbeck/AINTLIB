# Reviewer reply — 2026-06-24 (verbatim)

## Executive verdict

For **Leaf A / Prop. 8.30**, sidestep the general non-domain valuative criterion. Wedhorn's
Remark 7.55 reduces an arbitrary rational subset to a chain of **basic Laurent steps**, handled
directly by the already-proved basic flatness theorems. The general theorem
"∀ y ∈ Spa(B,B⁺), y(x) ≤ 1 ⇒ x power-bounded" is true in the correct affinoid setup but is
**not necessary on the critical path to Prop. 8.30** if Remark 7.55 is formalised as Wedhorn does.

For the long-term library, the right general non-domain theorem is **Wedhorn Prop. 7.18**, not a
minimal-prime reduction. The current domain-only valuative criterion is too narrow, and the
`PlusSubring` abstraction is missing a core affinoid-ring axiom.

- Q-bdd-2: yes, specialize the Prop. 8.30 proof to basic Laurent steps and skip general LL-bdd
  for Leaf A.
- Q-bdd-1: if you later need the general theorem, prove non-domain Wedhorn 7.18 / fix the
  plus-subring API; do not use minimal-prime patching as the main route.

## Q-bdd-1 — General non-domain power-boundedness criterion

The right theorem is **Wedhorn 7.18**, not minimal-prime patching. Def 7.14 includes B⁺ ⊆ Bᵒ;
Prop 7.18 reverses A' ↦ {v cont. | v(a)≤1 ∀a∈A'} for open integrally closed subrings, so for a
genuine ring of integral elements B⁺: (∀v∈Spa(B,B⁺), v(x)≤1) ⇒ x∈B⁺ ⊆ Bᵒ ⇒ x power-bounded.
This is NOT a domain theorem (Huber/Wedhorn valuations have prime support + valuation on a domain
quotient). Minimal-prime reduction is harder (completions/localisations not clean componentwise;
nilradicals/boundedness need patching; integrality doesn't commute with quotienting naively).

`PlusSubring` abstraction missing an axiom: if B⁺ is just a designated subring, x∈B⁺ →
IsPowerBounded x is NOT available. Fix (preferred): include B⁺ ⊆ Bᵒ (or plus_le_powerBounded).
Fix (local Path-α): keep hplus : B⁺ ⊆ P.A₀ (ring of definition bounded ⇒ power-bounded);
document as a local replacement for the missing axiom.

Direct restriction-map preservation of power-boundedness is true for bounded/adic morphisms but
not arbitrary continuous homs; state it as boundedness of the specific restriction map.

## Q-bdd-2 — Can Prop. 8.30 avoid general (LL-bdd)? YES.

After replacing V by Spa B (B=O(V), Example 6.38), Remark 7.55 reduces U to a chain
Spa B = X₋₁ ⊇ X₀ ⊇ … ⊇ Xₙ = U where each step is R(f/1)={x(f)≤1} or R(1/f)={x(f)≥1}. These are
Lemma 8.31's two flatness cases: O(R(f/1)) ≅ B⟨X⟩/(f-X), O(R(1/f)) ≅ B⟨X⟩/(1-fX). **Lemma 8.31
handles arbitrary f ∈ B** — does NOT require f power-bounded in the old base; the localization
makes f or 1/f power-bounded in the target.

Prop 8.30 proof: (1) Example 6.38 to V=Spa B; (2) Remark 7.55 factor U into basic Laurent steps;
(3) per step apply flat_quotient_fSubX_general / flat_quotient_oneSubfX_general; (4) compose flat
maps. No general (LL-bdd).

**Correction to the premise:** the chain does NOT guarantee the numerator lies in a pre-existing
ring of definition; the element may be t_i/s in the current section ring. That's fine — basic
plus datum R(f/1) is valid for arbitrary f (denominator 1 makes hopen trivial; the ring of
definition is enlarged by adjoining f). The right statement: "Remark 7.55 only uses basic Laurent
steps, and the basic Laurent flatness theorem handles arbitrary f." If the already-proved single
basic-Laurent flatness theorem assumes the numerator is in a ring of definition, it is too
narrow; align with Lemma 8.31 (all f ∈ B).

## Practical recommendation for Leaf A

Do NOT prove a general hasLocLiftPowerBounded_of_complete_stronglyNoetherianTate as a Prop 8.30
prerequisite. Instead prove prop_8_30_flat_via_remark_7_55: reduce to V=Spa B, factor U by 7.55
into basic steps, each step flat by flat_quotient_*_general (cases plus f / minus f), compose.
Still need (LL-unit) for constructing t_i/s (already proved).

## General (LL-bdd): future infrastructure, not Leaf A keystone

If later needed, prove via non-domain Wedhorn 7.18 (mem_plusSubring_of_forall_spa_vle_one +
isPowerBounded_of_forall_spa_vle_one with plus_le_powerBounded), not minimal-prime. Do not block
Prop 8.30 on this.
