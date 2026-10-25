import Dubon2026.SourceModularCharTwoDifferentialSum
import Dubon2026.SourceModularCoefficientWildGenusCriterion
import Dubon2026.SourceModularCoefficientDivisorSupport

/-! The characteristic-two lower genus bound on the actual modular
coefficient field. Finite divisor support supplies the census set and
the proved differential sum discharges the wild Hurwitz input. This is
the reverse inequality required by the DUB-17/18 residue genus comparison. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve SourceLevelProjective

theorem coeff_genus_lower_of_char_two (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K 2] (hNK : (N : K) ≠ 0) :
    genusFormula N ≤ (genusFF K (modularFunctionFieldCoeff N K) : ℚ) := by
  classical
  have hf : {v : Place K (modularFunctionFieldCoeff N K) |
      0 < v.ord (jCoeff N K)}.Finite :=
    (finite_coeff_divisor_support N K (jCoeff N K)).subset fun _ hv => ne_of_gt hv
  apply coeff_genus_lower_of_wild_differential_contribution N K hNK hf.toFinset
    (fun v hv => le_of_lt (hf.mem_toFinset.mp hv))
  exact coeff_char_two_differential_contribution N K hNK hf.toFinset
    (fun _ => hf.mem_toFinset)

end
end Dubon2026.SourceFunctionField
