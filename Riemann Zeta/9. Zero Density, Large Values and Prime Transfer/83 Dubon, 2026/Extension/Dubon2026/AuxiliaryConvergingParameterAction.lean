import Dubon2026.AuxiliaryParameterKernelBound

/-! The actual auxiliary group algebra carries a single constructed
continuous parameter action whose kernel lies in every maximal-adic
power up to its selected congruence level. This is the coefficient-ideal
convergence obligation in DUB-17's arithmetic patching dependency. -/

namespace Dubon2026
noncomputable section
open IsLocalRing
open scoped MvPowerSeries.WithPiTopology

/-- Construct one action with all required finite-level kernel bounds;
the map, continuity and bounds are conclusions, not supplied certificates. -/
theorem auxiliaryGroupAlgebra_exists_converging_parameterMap
    (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    {η ι : Type} [Fintype η] [Fintype ι] [DecidableEq ι]
    (Q : Finset Nat.Primes) (q level : ℕ) [Fact q.Prime] [CharP (ResidueField O) q]
    (e : η ≃ Q × ι) (hmod : ∀ p : Q, p.val.val ≡ 1 [MOD q ^ level])
    (g : ∀ p : Q, RationalPrimeTameCoefficientQuotient p.val.val q)
    (hg : ∀ p d, ∃ j : ℕ, g p ^ j = d) :
    let D := ∀ p : Q, ι → RationalPrimeTameCoefficientQuotient p.val.val q
    letI : TopologicalSpace (MonoidAlgebra O D) := moduleTopology O (MonoidAlgebra O D)
    ∃ f : MvPowerSeries η O →ₐ[O] MonoidAlgebra O D,
      (∀ j, f (MvPowerSeries.X j) = MonoidAlgebra.of O D
        (Pi.mulSingle (e j).1 (Pi.mulSingle (e j).2 (g (e j).1))) - 1) ∧
      IsLocalHom f.toRingHom ∧ Continuous f ∧
      ∀ n ≤ level, RingHom.ker f.toRingHom ≤ maximalIdeal (MvPowerSeries η O) ^ n := by
  obtain ⟨f, hf, hfl, hfc⟩ := auxiliaryGroupAlgebra_exists_powerSeriesMap O Q q e g
  refine ⟨f, hf, hfl, hfc, ?_⟩
  intro n hn
  exact auxiliaryGroupAlgebra_parameter_kernel_le O Q q level n e hn hmod g hg f hf hfc

end
end Dubon2026
