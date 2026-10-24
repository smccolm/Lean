import Dubon2026.SourceCurveWildDerivativeOrder
import Dubon2026.SourceModularCoefficientDerivativeOrders

/-! DUB-17/18 -> wild modular good reduction -> reverse genus -> local
differential contribution. All local differential hypotheses are derived
for the actual modular coefficient field. The three displayed estimates
are precisely the nonmaximal wild orders required by the source census. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N] (K : Type*) [Field K] [PerfectField K]

theorem coeff_place_ord_j_le_D_j_of_cast_eq_zero
    (v : Place K (modularFunctionFieldCoeff N K))
    (hcast : (v.ord (jCoeff N K) : K) = 0) :
    v.ord (jCoeff N K) ≤ v.ordDifferential (D K (modularFunctionFieldCoeff N K) (jCoeff N K)) := by
  haveI := finite_coeff_place_differentials N K v
  haveI := coeff_place_residue_isAlgebraic N K v
  haveI : Algebra.IsSeparable K v.ResidueField := inferInstance
  haveI := coeff_place_dCoordGenerates N K v
  haveI : Nontrivial Ω[modularFunctionFieldCoeff N K⁄K] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_coeff_differentials N K)
  exact v.ord_le_ordDifferential_D_of_cast_eq_zero hcast (D_jCoeff_ne_zero N K)

theorem coeff_place_three_le_D_j_of_char_three [CharP K 3]
    (v : Place K (modularFunctionFieldCoeff N K)) (hv : v.ord (jCoeff N K) = 3) :
    3 ≤ v.ordDifferential (D K (modularFunctionFieldCoeff N K) (jCoeff N K)) := by
  have hc : (v.ord (jCoeff N K) : K) = 0 := by
    rw [hv]
    exact_mod_cast CharP.cast_eq_zero K 3
  simpa only [hv] using coeff_place_ord_j_le_D_j_of_cast_eq_zero N K v hc

theorem coeff_place_four_le_D_j_of_char_two [CharP K 2]
    (v : Place K (modularFunctionFieldCoeff N K)) (hv : v.ord (jCoeff N K) = 4) :
    4 ≤ v.ordDifferential (D K (modularFunctionFieldCoeff N K) (jCoeff N K)) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hc : (v.ord (jCoeff N K) : K) = 0 := by
    rw [hv]
    norm_num only [Int.cast_ofNat]
    linear_combination 2 * h2
  simpa only [hv] using coeff_place_ord_j_le_D_j_of_cast_eq_zero N K v hc

theorem coeff_place_six_le_D_j_of_char_two [CharP K 2]
    (v : Place K (modularFunctionFieldCoeff N K)) (hv : v.ord (jCoeff N K) = 6) :
    6 ≤ v.ordDifferential (D K (modularFunctionFieldCoeff N K) (jCoeff N K)) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hc : (v.ord (jCoeff N K) : K) = 0 := by
    rw [hv]
    norm_num only [Int.cast_ofNat]
    linear_combination 3 * h2
  simpa only [hv] using coeff_place_ord_j_le_D_j_of_cast_eq_zero N K v hc

end
end Dubon2026.SourceFunctionField
