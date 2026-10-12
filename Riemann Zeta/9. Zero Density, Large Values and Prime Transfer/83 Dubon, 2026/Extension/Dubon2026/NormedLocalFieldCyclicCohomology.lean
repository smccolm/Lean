import Dubon2026.LocalFieldCyclicSecondCohomologyOrder
import Dubon2026.SpectralFiniteExtensionLocalField
import Mathlib.Analysis.Normed.Algebra.Basic

/-! # The genuine cyclic local H2 calculation for original normed field extensions -/

namespace Dubon2026
noncomputable section

/-- An original normed field extension preserves the actual norm
valuation relation under its actual algebra map. -/
theorem normedFieldValuation_hasExtension
    (K L : Type) [NontriviallyNormedField K] [NontriviallyNormedField L]
    [IsUltrametricDist K] [IsUltrametricDist L] [NormedAlgebra K L] :
    letI : ValuativeRel K := ValuativeRel.ofValuation (NormedField.valuation (K := K))
    letI : ValuativeRel L := ValuativeRel.ofValuation (NormedField.valuation (K := L))
    (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) := by
  letI : ValuativeRel K := ValuativeRel.ofValuation (NormedField.valuation (K := K))
  letI : ValuativeRel L := ValuativeRel.ofValuation (NormedField.valuation (K := L))
  haveI : (NormedField.valuation (K := K)).Compatible := Valuation.Compatible.ofValuation _
  haveI : (NormedField.valuation (K := L)).Compatible := Valuation.Compatible.ofValuation _
  constructor
  intro x y
  change ValuativeRel.valuation K x ≤ ValuativeRel.valuation K y ↔
    ValuativeRel.valuation L (algebraMap K L x) ≤ ValuativeRel.valuation L (algebraMap K L y)
  rw [ValuativeRel.isEquiv (ValuativeRel.valuation K) (NormedField.valuation (K := K)) x y,
    ← ValuativeRel.isEquiv (NormedField.valuation (K := L)) (ValuativeRel.valuation L)
      (algebraMap K L x) (algebraMap K L y)]
  change ‖x‖₊ ≤ ‖y‖₊ ↔ ‖algebraMap K L x‖₊ ≤ ‖algebraMap K L y‖₊
  simp only [nnnorm_algebraMap']

/-- The actual cyclic local H2 order theorem applies to the original
normed field extension, using its original topology and norm valuation. -/
theorem normedLocalField_cyclic_second_cohomology_order
    (K L : Type) [NontriviallyNormedField K] [NontriviallyNormedField L]
    [IsUltrametricDist K] [IsUltrametricDist L] [NormedAlgebra K L]
    [LocallyCompactSpace K] [LocallyCompactSpace L]
    [IsGalois K L] [IsCyclic Gal(L/K)] :
    Finite (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ∧
      Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) = Nat.card Gal(L/K) := by
  letI : ValuativeRel K := ValuativeRel.ofValuation (NormedField.valuation (K := K))
  letI : ValuativeRel L := ValuativeRel.ofValuation (NormedField.valuation (K := L))
  haveI : IsNonarchimedeanLocalField K := normValuation_isNonarchimedeanLocalField K
  haveI : IsNonarchimedeanLocalField L := normValuation_isNonarchimedeanLocalField L
  haveI := normedFieldValuation_hasExtension K L
  exact localField_cyclic_second_cohomology_order K L

end
end Dubon2026
