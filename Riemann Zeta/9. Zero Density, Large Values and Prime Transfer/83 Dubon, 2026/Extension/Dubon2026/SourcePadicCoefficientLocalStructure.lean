import Dubon2026.SpectralValuationExtension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! DUB-17/18 -> residual specialization of the constructed primitive
Galois representation -> a genuine local coefficient field with the same
canonical module topology. Reuse the proved spectral finite-extension
valuation and native finite-dimensional topology theorem. -/
namespace Dubon2026
noncomputable section

theorem padicFiniteCoefficient_local_structure (p : ℕ) [Fact p.Prime]
    (E : Type) [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E] :
    letI : ValuativeRel ℚ_[p] :=
      ValuativeRel.ofValuation (NormedField.valuation (K := ℚ_[p]))
    ∃ (_ : UniformSpace E) (_ : ValuativeRel E),
      IsUniformAddGroup E ∧ IsNonarchimedeanLocalField E ∧
      IsModuleTopology ℚ_[p] E ∧
      (ValuativeRel.valuation ℚ_[p]).HasExtension (ValuativeRel.valuation E) := by
  letI : ValuativeRel ℚ_[p] :=
    ValuativeRel.ofValuation (NormedField.valuation (K := ℚ_[p]))
  letI : (NormedField.valuation (K := ℚ_[p])).Compatible :=
    Valuation.Compatible.ofValuation _
  letI : NontriviallyNormedField E := spectralNorm.nontriviallyNormedField ℚ_[p] E
  letI : NormedAlgebra ℚ_[p] E := spectralNorm.normedAlgebra ℚ_[p] E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  letI : ValuativeRel E := ValuativeRel.ofValuation (NormedField.valuation (K := E))
  exact ⟨inferInstance, inferInstance, inferInstance,
    spectralFiniteExtension_isNonarchimedeanLocalField ℚ_[p] E,
    isModuleTopologyOfFiniteDimensional,
    spectralValuation_hasExtension ℚ_[p] E⟩

end
end Dubon2026
