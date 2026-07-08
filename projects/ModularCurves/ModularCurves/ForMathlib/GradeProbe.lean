import Mathlib
open CategoryTheory Abelian Limits ModuleCat
open scoped ModuleCat.Algebra

-- Probe A: Linear S (ModuleCat L) via scoped instance
example {S : Type} [CommRing S] (q : PrimeSpectrum S) :
    CategoryTheory.Linear S (ModuleCat.{0} (Localization q.asIdeal.primeCompl)) := inferInstance

-- Probe B: Module S on Ext over L
example {S : Type} [CommRing S] (q : PrimeSpectrum S)
    (X Y : ModuleCat.{0} (Localization q.asIdeal.primeCompl)) (n : ℕ) :
    Module S (Ext X Y n) := inferInstance

-- Probe C: the localization functor is S-linear
example {S : Type} [CommRing S] [IsNoetherianRing S] (q : PrimeSpectrum S) :
    (ModuleCat.localizedModuleFunctor.{0} (R := S) q.asIdeal.primeCompl).Linear S := inferInstance

-- Probe D: mapExtLinearMap applies (S-linear comparison map)
noncomputable example {S : Type} [CommRing S] [IsNoetherianRing S] (q : PrimeSpectrum S)
    (X Y : ModuleCat.{0} S) (n : ℕ) :
    Ext X Y n →ₗ[S]
      Ext ((ModuleCat.localizedModuleFunctor.{0} q.asIdeal.primeCompl).obj X)
          ((ModuleCat.localizedModuleFunctor.{0} q.asIdeal.primeCompl).obj Y) n :=
  (ModuleCat.localizedModuleFunctor.{0} q.asIdeal.primeCompl).mapExtLinearMap S X Y n

-- Probe E: IsScalarTower S L on Ext (compatibility)
example {S : Type} [CommRing S] (q : PrimeSpectrum S)
    (X Y : ModuleCat.{0} (Localization q.asIdeal.primeCompl)) (n : ℕ) :
    IsScalarTower S (Localization q.asIdeal.primeCompl) (Ext X Y n) := inferInstance
