import Dubon2026.SourceCurveDerivativeLowerOrder
import Dubon2026.SourceModularCoefficientLocalDifferentials

/-! DUB-17/18 -> good reduction -> reverse genus inequality -> Hurwitz
contribution of the finite j fibers and poles. The actual j differential is
nonzero, and all integral local-generation hypotheses have been proved.
This supplies the local order inequality in every residue characteristic. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N] (K : Type*) [Field K] [PerfectField K]

theorem coeff_place_ord_sub_one_le_D_j (v : Place K (modularFunctionFieldCoeff N K)) (a : K) :
    v.ord (jCoeff N K - algebraMap K (modularFunctionFieldCoeff N K) a) - 1 ≤
      v.ordDifferential (D K (modularFunctionFieldCoeff N K) (jCoeff N K)) := by
  haveI := finite_coeff_place_differentials N K v
  haveI := coeff_place_residue_isAlgebraic N K v
  haveI : Algebra.IsSeparable K v.ResidueField := inferInstance
  haveI := coeff_place_dCoordGenerates N K v
  haveI : Nontrivial Ω[modularFunctionFieldCoeff N K⁄K] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_coeff_differentials N K)
  have he : D K (modularFunctionFieldCoeff N K)
      (jCoeff N K - algebraMap K (modularFunctionFieldCoeff N K) a) =
        D K (modularFunctionFieldCoeff N K) (jCoeff N K) := by
    rw [map_sub, Derivation.map_algebraMap, sub_zero]
  have hD := he ▸ D_jCoeff_ne_zero N K
  simpa only [he] using v.ord_sub_one_le_ordDifferential_D hD

theorem coeff_place_ord_j_sub_one_le_D_j (v : Place K (modularFunctionFieldCoeff N K)) :
    v.ord (jCoeff N K) - 1 ≤
      v.ordDifferential (D K (modularFunctionFieldCoeff N K) (jCoeff N K)) := by
  simpa only [map_zero, sub_zero] using coeff_place_ord_sub_one_le_D_j N K v 0

end
end Dubon2026.SourceFunctionField
