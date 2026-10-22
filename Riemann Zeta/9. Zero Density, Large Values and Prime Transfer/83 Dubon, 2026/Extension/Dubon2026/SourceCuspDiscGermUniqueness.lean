import Dubon2026.SourceCuspDiscRealization

/-! DUB-17/18 -> original torsion cardinality -> actual cusp place chart.
Two meromorphic realizations of the same literal Laurent series agree
as punctured germs at every point of their common disk. Native connected
meromorphic uniqueness extends the proved Taylor quotient uniqueness.
This is the consistency needed for the order-map field laws.
-/
namespace Dubon2026.SourceFunctionField.CuspTaylor
noncomputable section
open Filter Metric
open scoped Topology

theorem Represents.eventuallyEq_on_disc {A : LaurentSeries ℂ} {F G : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hF : MeromorphicOn F (ball 0 R)) (hG : MeromorphicOn G (ball 0 R))
    (hFA : Represents A F) (hGA : Represents A G) {z : ℂ} (hz : z ∈ ball 0 R) :
    F =ᶠ[𝓝[≠] z] G := by
  have h0 : meromorphicOrderAt (F - G) 0 = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr ((hFA.unique hGA).mono fun _ hw => sub_eq_zero.mpr hw)
  have hz0 : meromorphicOrderAt (F - G) z = ⊤ := by
    by_contra hne
    exact (hF.sub hG).meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_ball (0 : ℂ) R).isPreconnected hz (mem_ball_self hR) hne h0
  exact (meromorphicOrderAt_eq_top_iff.mp hz0).mono fun _ hw => sub_eq_zero.mp hw

theorem Represents.order_eq_on_disc {A : LaurentSeries ℂ} {F G : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hF : MeromorphicOn F (ball 0 R)) (hG : MeromorphicOn G (ball 0 R))
    (hFA : Represents A F) (hGA : Represents A G) {z : ℂ} (hz : z ∈ ball 0 R) :
    meromorphicOrderAt F z = meromorphicOrderAt G z :=
  meromorphicOrderAt_congr (hFA.eventuallyEq_on_disc hR hF hG hGA hz)

end
end Dubon2026.SourceFunctionField.CuspTaylor
