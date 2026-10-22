import Dubon2026.SourceOriginalMeromorphicPoleBound
import Dubon2026.SourceOriginalMeromorphicRRBounds
import Dubon2026.SourceOriginalChartReadFieldLaws

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
original-function comparison. Every analytic meromorphic function on the
actual original curve admits a nonzero original multiplier that leaves poles
at only one chosen place. Compactness supplies the effective pole divisor;
the proved Riemann-Roch inequality constructs the multiplier.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Topology
variable (N : ℕ) [NeZero N]

theorem exists_original_meromorphic_pole_clearing
    (Q : Place ℂ (modularFunctionFieldOver N ℂ))
    (g : Place ℂ (modularFunctionFieldOver N ℂ) → ℂ)
    (hg : ∀ v, MeromorphicAt (fun z => g (placeFamily N v z)) 0) :
    ∃ n : ℕ, ∃ h : modularFunctionFieldOver N ℂ, h ≠ 0 ∧
      ∀ v, MeromorphicAt ((fun z => g (placeFamily N v z)) * chartRead N v h) 0 ∧
        ((-(Finsupp.single Q (n : ℤ)) v : ℤ) : WithTop ℤ) ≤
          meromorphicOrderAt ((fun z => g (placeFamily N v z)) * chartRead N v h) 0 := by
  obtain ⟨E, _, hE⟩ := exists_original_effective_meromorphic_pole_bound N g hg
  obtain ⟨n, h, hh0, hh⟩ := exists_original_pole_clearing_function N Q E
  refine ⟨n, h, hh0, fun v => ?_⟩
  have hm := meromorphicAt_chartRead N v h (Metric.mem_ball_self (place_spec N v).1)
  refine ⟨(hg v).mul hm, ?_⟩
  have hl := add_le_add (hE v) (chartRead_lSpace_order_bound N _ hh v)
  rw [← WithTop.coe_add, ← meromorphicOrderAt_mul (hg v) hm] at hl
  have he : -E v + -(Finsupp.single Q (n : ℤ) - E) v =
      -(Finsupp.single Q (n : ℤ)) v := by
    simp only [Finsupp.sub_apply]
    ring
  rwa [he] at hl

end
end Dubon2026.SourceFunctionField.OriginalChart
