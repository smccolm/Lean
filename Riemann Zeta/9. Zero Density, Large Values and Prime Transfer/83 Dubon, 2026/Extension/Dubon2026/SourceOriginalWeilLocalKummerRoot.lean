import Dubon2026.SourceMeromorphicKummerRoots
import Dubon2026.SourceOriginalChartFiberData

/-! DUB-17/18 -> auxiliary Kummer point division -> actual local roots.
For the original torsion radicand div(f)=nD, every proved original chart
admits a meromorphic n-th root of its actual evaluation reading, with order
D(v). No local-root, chart-existence or order premise beyond the actual
torsion divisor equation is assumed. Global cover/Picard work remains. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Metric
open scoped Topology
variable (N : ℕ) [NeZero N]
local notation "FF" => modularFunctionFieldOver N ℂ

theorem originalWeil_local_kummer_root (n : ℕ) [NeZero n]
    (D : Divisor ℂ FF) (f : FF) (hf : f ≠ 0)
    (hfD : ∀ v : Place ℂ FF, v.ord f = (n : ℤ) * D v) (v : Place ℂ FF) :
    ∃ H : ℂ → ℂ, MeromorphicAt H 0 ∧ meromorphicOrderAt H 0 = D v ∧
      ∀ᶠ z in 𝓝[≠] (0 : ℂ), H z ^ n = originalPlaceEval N ℂ (placeFamily N v z) f := by
  have hm := ((place_spec N v).2.2.1 0 (mem_ball_self (place_spec N v).1) f hf).1
  have ho := meromorphicOrderAt_place_reading N v hf
  rw [hfD] at ho
  exact AnalyticFiber.exists_meromorphic_kummer_root hm n (Nat.pos_of_ne_zero (NeZero.ne n)) (D v) ho

end
end Dubon2026.SourceFunctionField.OriginalChart
