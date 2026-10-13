import Dubon2026.NormedFieldPowerSmallBall
import Mathlib.Analysis.Normed.Ring.Ultra

/-! # The original small unit balls as open subgroups

These are the actual finite-place unit neighborhoods used to turn the exact
power-map ball image into the integer-unit power index required by DUB-17.
-/

namespace Dubon2026
noncomputable section
open Metric

variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]

/-- A field element at distance less than one from one has norm one. -/
theorem normedField_norm_eq_one_of_sub_lt {x : K} (hx : ‖x - 1‖ < 1) :
    ‖x‖ = 1 := by
  have hne : ‖x - 1‖ ≠ ‖(1 : K)‖ := by simpa only [norm_one] using hx.ne
  have h := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
  simpa only [sub_add_cancel, norm_one, max_eq_right hx.le] using h

/-- The actual original field units in a closed ball at one form a subgroup. -/
def normedFieldSmallUnitSubgroup (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Subgroup Kˣ where
  carrier := {u | ‖(u : K) - 1‖ ≤ r}
  one_mem' := by simpa using hr0
  mul_mem' := by
    intro u v hu hv
    have hv1 := normedField_norm_eq_one_of_sub_lt K (hv.trans_lt hr1)
    change ‖(u : K) * (v : K) - 1‖ ≤ r
    have he : (u : K) * (v : K) - 1 = ((u : K) - 1) * (v : K) + ((v : K) - 1) := by ring
    rw [he]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (by simpa only [norm_mul, hv1, mul_one] using hu) hv)
  inv_mem' := by
    intro u hu
    have hu1 := normedField_norm_eq_one_of_sub_lt K (hu.trans_lt hr1)
    change ‖((u⁻¹ : Kˣ) : K) - 1‖ ≤ r
    rw [Units.val_inv_eq_inv_val]
    have he : (u : K)⁻¹ - 1 = -((u : K) - 1) / (u : K) := by
      field_simp
      ring
    rw [he, norm_div, norm_neg, hu1, div_one]
    exact hu

/-- Positive-radius original small unit subgroups are open in the original
unit topology. -/
theorem normedFieldSmallUnitSubgroup_isOpen (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    IsOpen (normedFieldSmallUnitSubgroup K r hr0.le hr1 : Set Kˣ) := by
  have he : (normedFieldSmallUnitSubgroup K r hr0.le hr1 : Set Kˣ) =
      (fun u : Kˣ => (u : K)) ⁻¹' closedBall (1 : K) r := by
    ext u
    change ‖(u : K) - 1‖ ≤ r ↔ dist (u : K) 1 ≤ r
    rw [dist_eq_norm]
  rw [he]
  exact (IsUltrametricDist.isOpen_closedBall (1 : K) hr0.ne').preimage Units.continuous_val

end
end Dubon2026
