import Dubon2026.NormedFieldUnitPowerOpen
import Mathlib.Analysis.Normed.Group.Ultra

/-! # Exact local norm scaling for the original power map

The finite-place power-index input to the global norm-index upper bound in
DUB-17 needs only a sufficiently small unit neighborhood. The derivative and
ultrametric norm give its exact scaling, without a classification of all
principal units as a p-adic module.
-/

namespace Dubon2026
noncomputable section
open Filter Topology

variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]

/-- Near the original unit one, the actual power map scales the distance to
one by exactly the norm of its nonzero exponent. -/
theorem normedField_power_norm_sub_eventually (n : ℕ) (hn : (n : K) ≠ 0) :
    ∀ᶠ x : K in 𝓝 1, ‖x ^ n - 1‖ = ‖(n : K)‖ * ‖x - 1‖ := by
  have hd : HasDerivAt (fun x : K => x ^ n) (n : K) 1 := by
    simpa only [id_eq, one_pow, mul_one] using (hasDerivAt_id (1 : K)).pow n
  have hnpos : 0 < ‖(n : K)‖ := norm_pos_iff.mpr hn
  filter_upwards [hd.isLittleO.bound (half_pos hnpos)] with x hx
  by_cases he : x = 1
  · subst x
    simp
  have hxpos : 0 < ‖x - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
  have herr : ‖x ^ n - 1 - (x - 1) * (n : K)‖ < ‖(x - 1) * (n : K)‖ := by
    simp only [one_pow, smul_eq_mul] at hx
    rw [norm_mul]
    exact hx.trans_lt (by nlinarith)
  have hsum := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm herr.ne
  rw [sub_add_cancel, max_eq_right herr.le, norm_mul] at hsum
  exact hsum.trans (mul_comm _ _)

end
end Dubon2026
