import Dubon2026.RationalPrimeAuxiliaryCyclicParameters
import Dubon2026.AuxiliaryCharacterParameterConvergence

/-! The actual tame character augmentation is the image of the variable
ideal under one convergent power-series algebra map. This is the precise
coefficient-algebra input to the common-parameter patching construction
on the DUB-17 automorphy dependency chain. -/

namespace Dubon2026
noncomputable section
open IsLocalRing
open MvPowerSeries.WithPiTopology

/-- The original tame character family constructs a power-series
parameter map whose variable ideal is exactly the actual augmentation
ideal. The original topology, cyclic generators and their evaluations
are retained. -/
theorem rationalPrimeAuxiliaryFamily_exists_powerSeries_parameters
    (O : Type*) [CommRing O] [UniformSpace O]
    [IsTopologicalRing O] [IsUniformAddGroup O]
    {ι A : Type*} [Fintype ι] [CommRing A] [IsLocalRing A] [Algebra O A]
    [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A] [T2Space A]
    [IsTopologicalRing A] [IsLinearTopology A A] [ContinuousSMul O A]
    (Q : Finset Nat.Primes) (q : ℕ)
    (κ : ∀ p : Q, RationalPrimeTameCoefficientQuotient p.val.val q →* (ι → A)ˣ)
    (hκ : ∀ p d i, residue A ((κ p d).val i) = 1)
    (hA : (inferInstance : TopologicalSpace A) = (maximalIdeal A).adicTopology) :
    ∃ g : ∀ p : Q, RationalPrimeTameCoefficientQuotient p.val.val q,
      ∃ e : MvPowerSeries (Q × ι) O →ₐ[O] A,
        (∀ p d, ∃ n : ℕ, g p ^ n = d) ∧
        (∀ pi : Q × ι, e (MvPowerSeries.X pi) = ((κ pi.1 (g pi.1)).val pi.2) - 1) ∧
        Continuous e ∧
        Ideal.map e.toRingHom (Ideal.span (Set.range (MvPowerSeries.X (R := O) (σ := Q × ι)))) =
          auxiliaryFamilyAugmentationIdeal O κ := by
  obtain ⟨g, hg, hspan⟩ := rationalPrimeAuxiliaryFamily_exists_augmentation_generators O Q q κ
  let hx := auxiliaryCharacterParameters_hasEval κ hκ hA g
  let e : MvPowerSeries (Q × ι) O →ₐ[O] A := MvPowerSeries.aeval hx
  have he (pi : Q × ι) : e (MvPowerSeries.X pi) = ((κ pi.1 (g pi.1)).val pi.2) - 1 := by
    change MvPowerSeries.aeval hx (MvPowerSeries.X pi) = _
    rw [MvPowerSeries.coe_aeval, MvPowerSeries.eval₂_X]
  refine ⟨g, e, hg, he, MvPowerSeries.continuous_aeval hx, ?_⟩
  rw [Ideal.map_span, ← Set.range_comp]
  change Ideal.span (Set.range fun pi : Q × ι => e (MvPowerSeries.X pi)) = _
  simpa only [he] using hspan.symm

end
end Dubon2026
