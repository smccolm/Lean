import Dubon2026.AuxiliaryFamilyPowerSeriesParameters
import Mathlib.RingTheory.AdicCompletion.Topology

/-! Adic completeness of the genuine coefficient ring supplies all
topological hypotheses needed to construct its power-series parameter
map. No separately supplied uniform structure, convergence certificate
or continuous scalar action is needed by the arithmetic consumer. -/

namespace Dubon2026
noncomputable section
open IsLocalRing

/-- A complete local coefficient algebra and its actual residue-one
tame characters construct the power-series parameter map and exact
augmentation image. All auxiliary topological structures are derived
inside the proof; the result is an algebra map of the original rings. -/
theorem completeLocalAuxiliaryFamily_exists_powerSeries_parameters
    (O : Type*) [CommRing O] {ι A : Type*}
    [Fintype ι] [CommRing A] [IsLocalRing A] [Algebra O A]
    [IsAdicComplete (maximalIdeal A) A]
    (Q : Finset Nat.Primes) (q : ℕ)
    (κ : ∀ p : Q, RationalPrimeTameCoefficientQuotient p.val.val q →* (ι → A)ˣ)
    (hκ : ∀ p d i, residue A ((κ p d).val i) = 1) :
    ∃ g : ∀ p : Q, RationalPrimeTameCoefficientQuotient p.val.val q,
      ∃ e : MvPowerSeries (Q × ι) O →ₐ[O] A,
        (∀ p d, ∃ n : ℕ, g p ^ n = d) ∧
        (∀ pi : Q × ι, e (MvPowerSeries.X pi) = ((κ pi.1 (g pi.1)).val pi.2) - 1) ∧
        Ideal.map e.toRingHom (Ideal.span (Set.range (MvPowerSeries.X (R := O) (σ := Q × ι)))) =
          auxiliaryFamilyAugmentationIdeal O κ := by
  letI : TopologicalSpace O := ⊥
  letI : DiscreteTopology O := ⟨rfl⟩
  letI : UniformSpace O := IsTopologicalAddGroup.rightUniformSpace O
  letI : IsUniformAddGroup O := isUniformAddGroup_of_addCommGroup
  letI : WithIdeal A := ⟨maximalIdeal A⟩
  have htop : IsAdic (maximalIdeal A) := rfl
  have hcomplete := htop.isAdicComplete_iff.mp (inferInstance : IsAdicComplete (maximalIdeal A) A)
  letI : CompleteSpace A := hcomplete.1
  letI : T2Space A := hcomplete.2
  letI : ContinuousSMul O A := ⟨by
    have hc : Continuous (algebraMap O A) := continuous_of_discreteTopology
    simpa only [Algebra.smul_def] using (hc.comp continuous_fst).mul continuous_snd⟩
  obtain ⟨g, e, hg, he, _, hJ⟩ :=
    rationalPrimeAuxiliaryFamily_exists_powerSeries_parameters O Q q κ hκ rfl
  exact ⟨g, e, hg, he, hJ⟩

end
end Dubon2026
