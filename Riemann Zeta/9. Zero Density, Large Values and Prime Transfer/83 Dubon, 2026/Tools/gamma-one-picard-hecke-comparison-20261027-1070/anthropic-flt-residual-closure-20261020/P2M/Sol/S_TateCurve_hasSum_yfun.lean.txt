import Definitions.Def_TateCurve_PointSeries
import P2M.Util
namespace P2MW.S_TateCurve_hasSum_yfun
open TateCurve
open scoped NNReal

theorem solution {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    {w : K} (hw : ‖w‖₊ < 1) :
    HasSum (fun m : ℕ => (((m + 2).choose 2 : ℕ) : K) * w ^ (m + 2)) (yfun w) := by
  have hw' : ‖w‖ < 1 := hw
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one 2 hw').mul_left (w ^ 2)
  have hfun : (fun m : ℕ => w ^ 2 * (((m + 2).choose 2 : ℕ) * w ^ m))
      = fun m : ℕ => (((m + 2).choose 2 : ℕ) : K) * w ^ (m + 2) := by
    funext m; ring
  have hval : w ^ 2 * (1 / (1 - w) ^ 3) = yfun w := by rw [yfun]; ring
  rw [hfun, hval] at h
  exact h
