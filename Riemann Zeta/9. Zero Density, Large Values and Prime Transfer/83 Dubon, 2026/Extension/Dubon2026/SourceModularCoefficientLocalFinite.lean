import Dubon2026.SourceCurveSeparatingLocalFinite
import Dubon2026.SourceModularCoefficientCurve
import Dubon2026.SourceCurveTranscendentalDegree

/-! DUB-17/18 -> good reduction -> reverse genus inequality -> actual local
differential orders. At every actual residue-field place, either j or its
inverse is integral. Their common separating rational field gives essential
finite type and finite integral differentials. This discharges the local
finiteness premise without introducing arbitrary-coordinate separability. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve IntermediateField KaehlerDifferential
variable (N : ℕ) [NeZero N] (K : Type*) [Field K] [PerfectField K]

theorem essFiniteType_coeff_place (v : Place K (modularFunctionFieldCoeff N K)) :
    Algebra.EssFiniteType K v.toValuationSubring := by
  haveI := finiteDimensional_coeff_field N K
  haveI := isSeparable_coeff_field N K
  rcases v.toValuationSubring.mem_or_inv_mem (jCoeff N K) with hj | hj
  · exact essFiniteType_place_of_separating_coordinate (jCoeff N K)
      (transcendental_jCoeff N K) v hj
  · have ht : Transcendental K (jCoeff N K)⁻¹ :=
      fun h => transcendental_jCoeff N K (IsAlgebraic.inv_iff.mp h)
    haveI : FiniteDimensional K⟮(jCoeff N K)⁻¹⟯ (modularFunctionFieldCoeff N K) := by
      rw [adjoin_singleton_inv_eq]
      infer_instance
    haveI : Algebra.IsSeparable K⟮(jCoeff N K)⁻¹⟯ (modularFunctionFieldCoeff N K) := by
      rw [adjoin_singleton_inv_eq]
      infer_instance
    exact essFiniteType_place_of_separating_coordinate (jCoeff N K)⁻¹ ht v hj

theorem finite_coeff_place_differentials (v : Place K (modularFunctionFieldCoeff N K)) :
    Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K] := by
  haveI := essFiniteType_coeff_place N K v
  exact KaehlerDifferential.finite K v.toValuationSubring

end
end Dubon2026.SourceFunctionField
