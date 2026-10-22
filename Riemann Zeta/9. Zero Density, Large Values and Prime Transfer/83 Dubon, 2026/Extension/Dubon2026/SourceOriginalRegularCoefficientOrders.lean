import Dubon2026.SourceOriginalRegularOrders
import Dubon2026.SourceOriginalJCoordinatePlaces

/-! DUB-17/18 -> matching cusp-form lower dimension -> analytic realization
of regular differentials. Express a regular differential as x D(j). Its
actual local coefficient order gives the precise bound needed to cancel
analytic branching. This is applied at the original analytic places next.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential

theorem original_regular_coefficient_order_bound (N : ℕ) [NeZero N]
    (x : modularFunctionFieldOver N ℂ) (hx : x ≠ 0)
    (hreg : x • D ℂ (modularFunctionFieldOver N ℂ) (jOver N ℂ) ∈
      regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    (v : Place ℂ (modularFunctionFieldOver N ℂ)) (c : ℂ)
    (hc : 0 < v.ord (jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) c)) :
    1 - v.ord (jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) c) ≤ v.ord x := by
  haveI := original_place_dCoordGenerates N ℂ v
  haveI : Nontrivial Ω[modularFunctionFieldOver N ℂ⁄ℂ] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_original_differentials N ℂ)
  have hcoeff : v.differentialCoeff (D ℂ (modularFunctionFieldOver N ℂ) (jOver N ℂ)) ≠ 0 := by
    intro he
    have h := v.differentialCoeff_smul_dCoord (D ℂ (modularFunctionFieldOver N ℂ) (jOver N ℂ))
    rw [he, zero_smul] at h
    exact D_jOver_ne_zero N ℂ h.symm
  have hr := (mem_original_regularDifferentials_iff_ord_nonneg N ℂ _).mp hreg v
  rw [v.ordDifferential_smul hx hcoeff] at hr
  have hD : D ℂ (modularFunctionFieldOver N ℂ)
      (jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) c) =
        D ℂ (modularFunctionFieldOver N ℂ) (jOver N ℂ) := by
    rw [map_sub, Derivation.map_algebraMap, sub_zero]
  have ho := original_ordDifferential_D_eq_ord_sub_one N ℂ v hc.ne'
  rw [hD] at ho
  omega

end
end Dubon2026.SourceFunctionField
