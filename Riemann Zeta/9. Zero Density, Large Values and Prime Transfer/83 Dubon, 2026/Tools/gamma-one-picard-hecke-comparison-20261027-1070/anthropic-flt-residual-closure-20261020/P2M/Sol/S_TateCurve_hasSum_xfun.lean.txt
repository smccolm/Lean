import Definitions.Def_TateCurve_PointSeries
import P2M.Util
namespace P2MW.S_TateCurve_hasSum_xfun
open TateCurve
open scoped NNReal

theorem solution {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    {w : K} (hw : ‖w‖₊ < 1) :
    HasSum (fun m : ℕ => ((m + 1 : ℕ) : K) * w ^ (m + 1)) (xfun w) := by
  have hw' : ‖w‖ < 1 := hw
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one 1 hw').mul_left w
  have hfun : (fun m : ℕ => w * (((m + 1).choose 1 : ℕ) * w ^ m))
      = fun m : ℕ => ((m + 1 : ℕ) : K) * w ^ (m + 1) := by
    funext m; rw [Nat.choose_one_right]; ring
  have hval : w * (1 / (1 - w) ^ 2) = xfun w := by rw [xfun]; ring
  rw [hfun, hval] at h
  exact h
