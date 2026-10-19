import Dubon2026.AuxiliaryFixedPowerSeriesPatchingRing
import Dubon2026.AuxiliaryFixedParameterContinuity
import Dubon2026.AuxiliaryPatchingRingCardinality

/-! The common parameter algebra and its actual action satisfy the
ring-topology requirements of patching. All properties below are
derived from the original characters, residue comparison and compact
coefficient rings; arithmetic module freeness is not assumed or proved. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped MvPowerSeries.WithPiTopology BigOperators

variable (O : Type) {R A ι n G η : Type}
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [Finite (ResidueField O)]
  [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
  [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra O R]
  [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R] [T2Space R]
  [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra O A] [Fintype ι] [Fintype n] [DecidableEq n] [Fintype η]
  (Q : Finset Nat.Primes) (q : ℕ)
  (τ : G → GeneralLinearGroup n R) (τ₀ : G → GeneralLinearGroup n A)

/-- Construct the local continuous action and the exact compact,
Noetherian, adic and complete parameter-ring properties required by
patching, retaining the same scalar-compatible quotient comparison and deriving every finite-quotient cardinality bound from the fixed base ring and parameter index. -/
def auxiliaryBoundedTopologicalPatchingRingComparison
    (d : AuxiliaryFixedPowerSeriesPatchingRingComparison O (ι := ι) (η := η) Q q τ τ₀)
    (eR : ResidueField R ≃ₐ[O] ResidueField O) :
    {c : AuxiliaryFixedPowerSeriesPatchingRingComparison O (ι := ι) (η := η) Q q τ τ₀ //
      IsLocalHom (auxiliaryFixedPowerSeriesParameterMap O Q q τ τ₀ c.1).toRingHom ∧
      Continuous (auxiliaryFixedPowerSeriesParameterMap O Q q τ τ₀ c.1) ∧
      IsNoetherianRing (MvPowerSeries η O) ∧ CompactSpace (MvPowerSeries η O) ∧
      IsAdicTopology (MvPowerSeries η O) ∧
      IsAdicComplete (maximalIdeal (MvPowerSeries η O)) (MvPowerSeries η O) ∧
      ∀ k : ℕ, Nat.card (R ⧸ maximalIdeal R ^ k) ≤
        Nat.card (ResidueField O) ^
          (∑ i ∈ Finset.range k, (Fintype.card η + (localMaximalGenerators A).card) ^ i)} :=
  ⟨d, auxiliaryFixedPowerSeriesParameterMap_isLocal Q q τ τ₀ d.1 eR,
    auxiliaryFixedPowerSeriesParameterMap_continuous Q q τ τ₀ d.1 eR,
    finiteVariablePowerSeries_isNoetherian (R := O) η,
    finitePowerSeries_compactSpace, finitePowerSeries_isAdicTopology,
    finitePowerSeries_isAdicComplete,
    fun k => auxiliaryFixedPowerSeries_cardinality_pow_le O Q q τ τ₀ d.1 eR k⟩

end
end Dubon2026
