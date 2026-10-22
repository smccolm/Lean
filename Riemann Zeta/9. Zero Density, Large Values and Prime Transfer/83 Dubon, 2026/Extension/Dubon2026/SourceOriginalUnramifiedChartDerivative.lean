import Dubon2026.SourceOriginalChartFiberOrders

/-! DUB-17/18 -> geometric cell dissection -> analytic ordinary j sheets.
The proved exact original chart multiplicity and Mathlib's derivative-order
identity show that an order-one fiber has a nonzero coordinate derivative.
This supplies the derivative condition for the actual covering sheets.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Metric
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem deriv_chartRead_ne_zero_of_order_one (v : Place ℂ F) {f : F}
    (hf : f ∈ v.toValuationSubring)
    (ho : v.ord (f - algebraMap ℂ F (originalPlaceEval N ℂ v f)) = 1) :
    deriv (chartRead N v f) 0 ≠ 0 := by
  let c := originalPlaceEval N ℂ v f
  have hne : f - algebraMap ℂ F c ≠ 0 := by
    intro h
    rw [h, v.ord_zero] at ho
    norm_num at ho
  have hm : f ∈ (placeFamily N v 0).toValuationSubring := by rwa [(place_spec N v).2.1]
  obtain ⟨hfinite, hn⟩ := chartRead_order_sub N v (mem_ball_self (place_spec N v).1) hm c hne
  rw [(place_spec N v).2.1, ho] at hn
  have hn1 : analyticOrderNatAt (fun u => chartRead N v f u - c) 0 = 1 := by exact_mod_cast hn.symm
  have horder : analyticOrderAt (fun u => chartRead N v f u - c) 0 = 1 := by
    rw [← Nat.cast_analyticOrderNatAt hfinite, hn1]
    rfl
  have ha : AnalyticAt ℂ (chartRead N v f) 0 := analyticAt_place_reading N v hf
  have hval : chartRead N v f 0 = c := by rw [chartRead, (place_spec N v).2.1]
  have hd := ha.analyticOrderAt_deriv_add_one
  rw [hval, horder] at hd
  have hz : analyticOrderAt (deriv (chartRead N v f)) 0 = 0 :=
    ENat.add_left_injective_of_ne_top (by simp : (1 : ℕ∞) ≠ ⊤) (by simpa only [zero_add] using hd)
  exact ha.deriv.analyticOrderAt_eq_zero.mp hz

end
end Dubon2026.SourceFunctionField.OriginalChart
