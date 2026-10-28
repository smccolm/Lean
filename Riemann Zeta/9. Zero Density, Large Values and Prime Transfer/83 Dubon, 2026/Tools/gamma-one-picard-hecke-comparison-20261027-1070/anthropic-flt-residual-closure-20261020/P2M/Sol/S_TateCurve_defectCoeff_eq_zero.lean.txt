import Mathlib
import Definitions.Def_TateCurve_DefectLines
import Theorems.Thm_TateCurve_lineCoeff_eq_zero
import P2M.Util
namespace P2MW.S_TateCurve_defectCoeff_eq_zero

open TateCurve
open scoped NNReal

theorem solution {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [CharZero K] {u : K} (hu0 : u ≠ 0) (hu1 : u ≠ 1) {N : ℕ} (hN : 0 < N) :
    defectCoeff u N = 0 :=
  defectCoeff_eq_zero_of_lineCoeff_eq_zero hu0 hu1 hN fun k hk =>
    TateCurve.lineCoeff_eq_zero N k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2
