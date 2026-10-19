import Dubon2026.AuxiliaryFixedPowerSeriesComparison
import Dubon2026.PowerSeriesLocalParameterMap
import Dubon2026.FinitePowerSeriesPatchingTopology

/-! The actual fixed parameter map is local and continuous in the
original compact coefficient topologies. Its character values and
residue comparison derive these properties for the same data used in
the common-algebra quotient specialization on the DUB-17 chain. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped MvPowerSeries.WithPiTopology

variable {O R A : Type} {ι n G η : Type}
  [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R]
  [CommRing A] [Algebra O A] [Fintype ι] [Fintype n] [DecidableEq n] [Fintype η]
  (Q : Finset Nat.Primes) (q : ℕ)
  (τ : G → GeneralLinearGroup n R) (τ₀ : G → GeneralLinearGroup n A)

/-- The actual residue-one characters make the fixed parameter map
local. Locality of the original coefficient map is derived from its
residue algebra identification. -/
theorem auxiliaryFixedPowerSeriesParameterMap_isLocal
    (d : AuxiliaryFixedPowerSeriesComparison O (ι := ι) Q q τ τ₀ η)
    (eR : ResidueField R ≃ₐ[O] ResidueField O) :
    IsLocalHom (auxiliaryFixedPowerSeriesParameterMap O Q q τ τ₀ d).toRingHom := by
  letI := residueAlgebraEquiv_algebraMap_isLocal eR
  apply finitePowerSeries_parameterMap_isLocal
  intro i
  change auxiliaryPowerSeriesFixedParameterMap O Q q τ τ₀ d.comparison d.index
    (MvPowerSeries.X i) ∈ maximalIdeal R
  rw [auxiliaryPowerSeriesFixedParameterMap_X]
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change residue R
    ((d.comparison.augmentation.characters (d.index i).1
      (d.comparison.parameters.generators (d.index i).1)).val (d.index i).2 - 1) = 0
  rw [map_sub, map_one, d.comparison.augmentation.residue_one, sub_self]

/-- The original fixed parameter action is continuous under the
compact Hausdorff Noetherian coefficient hypotheses required by patching. -/
theorem auxiliaryFixedPowerSeriesParameterMap_continuous
    [IsNoetherianRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O]
    [IsNoetherianRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CompactSpace R] [T2Space R]
    (d : AuxiliaryFixedPowerSeriesComparison O (ι := ι) Q q τ τ₀ η)
    (eR : ResidueField R ≃ₐ[O] ResidueField O) :
    Continuous (auxiliaryFixedPowerSeriesParameterMap O Q q τ τ₀ d) := by
  letI := finiteVariablePowerSeries_isNoetherian (R := O) η
  letI := finitePowerSeries_compactSpace (O := O) (η := η)
  letI := auxiliaryFixedPowerSeriesParameterMap_isLocal Q q τ τ₀ d eR
  exact compactSeparatedLocalRingHom_continuous
    (auxiliaryFixedPowerSeriesParameterMap O Q q τ τ₀ d).toRingHom

end
end Dubon2026
