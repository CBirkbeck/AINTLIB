# Reviewer reply — (LL-bdd) follow-up — 2026-06-14

VERDICT: Q-bdd-2 YES — skip the general non-domain (LL-bdd) for Leaf A. Wedhorn's Remark 7.55
reduces an arbitrary rational subset to a chain of BASIC LAURENT STEPS R(f/1),R(1/f) for
ARBITRARY f ∈ B. Each step flat by Lemma 8.31(2): O(R(f/1))≅B⟨X⟩/(f-X), O(R(1/f))≅B⟨X⟩/(1-fX).
These flatness theorems handle ARBITRARY f — NO power-boundedness of f in the old base. The
rational localization itself makes f (or 1/f) power-bounded in the target. Compose flat maps.

CORRECTION to my premise: the chain does NOT guarantee numerators lie in a pre-existing ring of
definition. The plus step's element may be t_i/s in the current section ring, not in old A₀. That
is fine: R(f/1) is valid for arbitrary f because denominator 1 makes hopen trivial (ring of def
enlarged by adjoining f); R(1/f) valid for arbitrary f (numerator 1, localization adjoins 1/f).
⇒ If the already-proved single basic-Laurent flatness theorem currently ASSUMES numerator ∈ ring
of definition (e.g. prop_8_30_basic_laurent_step_flat's hD'_T_pb / LaurentNormalized T⊆A₀), it is
TOO NARROW — align it with Lemma 8.31(2) (arbitrary f).

Q-bdd-1 (general theorem, NOT on Leaf-A critical path; future infra): prove via non-domain Wedhorn
Prop 7.18, NOT minimal-prime patching. The clean route: all Spa valuations ≤1 ⇒ x∈B⁺ (Prop 7.18) ⇒
x∈Bᵒ (B⁺ ⊆ power-bounded, Wedhorn Def 7.14) ⇒ power-bounded.

PlusSubring API GAP: our PlusSubring is just a designated subring; missing the affinoid axiom
B⁺ ⊆ Bᵒ. Library fix: add `plus_le_powerBounded : ∀ x∈B⁺, IsPowerBounded x` (or B⁺⊆Bᵒ). Local
Path-α fix (acceptable now, document it): keep hplus : B⁺ ⊆ P.A₀, then x∈B⁺ ⇒ x∈P.A₀ ⇒ power-bounded
(ring of def bounded).

Restriction-map-preserves-PB: true for adic/bounded morphisms (not arbitrary continuous), but
proving it is another form of the same compatibility theorem; valuative route is cleaner — but if
plus API weak, a direct "this restriction map sends ring-of-def to bounded" lemma may be easier.

PROP 8.30 PROOF SHAPE: (1) Example 6.38 reduce V→B=O(V); (2) Remark 7.55 factor U into basic steps;
(3) each step flat via flat_quotient_fSubX_general / flat_quotient_oneSubfX_general (Lemma 8.31(2),
arbitrary f); (4) compose. NO general (LL-bdd), NO hasLocLiftPowerBounded_of_complete_stronglyNoeth
prerequisite.
