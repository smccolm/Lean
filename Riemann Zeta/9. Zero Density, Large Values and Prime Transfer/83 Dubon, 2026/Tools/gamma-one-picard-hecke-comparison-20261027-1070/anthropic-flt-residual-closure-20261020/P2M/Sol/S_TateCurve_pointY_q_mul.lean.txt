import Definitions.Def_TateCurve_PointSeries
import P2M.Util
namespace P2MW.S_TateCurve_pointY_q_mul
open TateCurve
open scoped NNReal

private theorem tsum_comp_add_one' {α : Type*} [AddCommGroup α] [UniformSpace α]
    [IsUniformAddGroup α] [CompleteSpace α] [T2Space α] (f : ℤ → α) :
    ∑' n : ℤ, f (n + 1) = ∑' n : ℤ, f n :=
  (Equiv.addRight (1 : ℤ)).tsum_eq f

theorem solution {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] {q u : K} (hq0 : q ≠ 0) : pointY q (q * u) = pointY q u := by
  have hterm : ∀ n : ℤ, yTerm q (q * u) n = yTerm q u (n + 1) := fun n => by
    rw [yTerm, yTerm, show q ^ n * (q * u) = q ^ (n + 1) * u by rw [zpow_add_one₀ hq0]; ring]
  rw [pointY, pointY]
  congr 1
  calc ∑' n : ℤ, yTerm q (q * u) n = ∑' n : ℤ, yTerm q u (n + 1) := tsum_congr hterm
    _ = ∑' n : ℤ, yTerm q u n := tsum_comp_add_one' _
