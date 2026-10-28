import Definitions.Def_TateCurve_PointSeries
import P2M.Util
namespace P2MW.S_TateCurve_pointX_inv

open TateCurve
open scoped NNReal

theorem solution {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] {q u : K} (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hu : ∀ n : ℤ, q ^ n * u ≠ 1) :
    pointX q u⁻¹ = pointX q u := by
  have hinv : ∀ n : ℤ, xTerm q u⁻¹ (-n) = xTerm q u n := fun n => by
    rw [xTerm, xTerm, zpow_neg, ← mul_inv]
    exact xfun_inv (mul_ne_zero (zpow_ne_zero n hq0) hu0) (hu n)
  rw [pointX, pointX]
  congr 1
  calc ∑' n : ℤ, xTerm q u⁻¹ n = ∑' n : ℤ, xTerm q u⁻¹ (-n) := (tsum_comp_neg _).symm
    _ = ∑' n : ℤ, xTerm q u n := tsum_congr hinv
