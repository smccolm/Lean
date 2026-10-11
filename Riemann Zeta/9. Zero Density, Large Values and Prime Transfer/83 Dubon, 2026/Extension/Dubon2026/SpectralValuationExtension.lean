import Dubon2026.SpectralFiniteExtensionLocalField
import Mathlib.RingTheory.Valuation.Extension

/-! # The actual spectral valuation extends the original compatible valuation -/

namespace Dubon2026
noncomputable section

/-- Equality of the spectral norm with the original base norm proves the
valuation extension property. The canonical extension valuation is constructed
on the genuine finite extension; no extension certificate is assumed. -/
theorem spectralValuation_hasExtension
    (K L : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
    [Field L] [Algebra K L] [FiniteDimensional K L] :
    letI : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := ValuativeRel.ofValuation (NormedField.valuation (K := L))
    (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) := by
  letI : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L := ValuativeRel.ofValuation (NormedField.valuation (K := L))
  haveI : (NormedField.valuation (K := L)).Compatible := Valuation.Compatible.ofValuation _
  constructor
  intro x y
  change ValuativeRel.valuation K x ≤ ValuativeRel.valuation K y ↔
    ValuativeRel.valuation L (algebraMap K L x) ≤
      ValuativeRel.valuation L (algebraMap K L y)
  calc
    ValuativeRel.valuation K x ≤ ValuativeRel.valuation K y ↔
        NormedField.valuation (K := K) x ≤ NormedField.valuation (K := K) y :=
      ValuativeRel.isEquiv (ValuativeRel.valuation K) (NormedField.valuation (K := K)) x y
    _ ↔ NormedField.valuation (K := L) (algebraMap K L x) ≤
        NormedField.valuation (K := L) (algebraMap K L y) := by
      change ‖x‖₊ ≤ ‖y‖₊ ↔ ‖algebraMap K L x‖₊ ≤ ‖algebraMap K L y‖₊
      rw [← NNReal.coe_le_coe, ← NNReal.coe_le_coe]
      change ‖x‖ ≤ ‖y‖ ↔
        spectralNorm K L (algebraMap K L x) ≤ spectralNorm K L (algebraMap K L y)
      rw [spectralNorm_extends, spectralNorm_extends]
    _ ↔ _ := ValuativeRel.isEquiv (NormedField.valuation (K := L))
      (ValuativeRel.valuation L) (algebraMap K L x) (algebraMap K L y)

end
end Dubon2026
