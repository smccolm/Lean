import Dubon2026.NormedFieldSmallUnitBalls

/-! # Actual power images and trivial kernels on sufficiently small units

This is the small-subgroup input to the finite-place numerical power index
in DUB-17's cyclic global norm-index dependency. The local inverse is proved,
not supplied as an additional arithmetic hypothesis.
-/

namespace Dubon2026
noncomputable section
open Metric

variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]

/-- Small original unit balls have precisely the scaled power image and
trivial intersection with the original power kernel. -/
theorem normedField_exists_small_unit_power_image (n : ℕ) (hn : (n : K) ≠ 0) :
    ∃ (r : ℝ) (_hr0 : 0 < r) (hr1 : r < 1), ∀ (s : ℝ) (hs0 : 0 < s) (hsr : s ≤ r),
      let hs1 : s < 1 := hsr.trans_lt hr1
      let ht1 : ‖(n : K)‖ * s < 1 :=
        (mul_le_of_le_one_left hs0.le (IsUltrametricDist.norm_natCast_le_one K n)).trans_lt hs1
      let U := normedFieldSmallUnitSubgroup K s hs0.le hs1
      let V := normedFieldSmallUnitSubgroup K (‖(n : K)‖ * s)
        (mul_nonneg (norm_nonneg _) hs0.le) ht1
      U.map (powMonoidHom n : Kˣ →* Kˣ) = V ∧
        U ⊓ (powMonoidHom n : Kˣ →* Kˣ).ker = ⊥ := by
  obtain ⟨r, hr0, hr1, hballs⟩ := normedField_power_small_closedBall K n hn
  refine ⟨r, hr0, hr1, ?_⟩
  intro s hs0 hsr
  dsimp only
  let U := normedFieldSmallUnitSubgroup K s hs0.le (hsr.trans_lt hr1)
  have hb := hballs s hs0 hsr
  constructor
  · ext u
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : (x : K) ∈ closedBall (1 : K) s := by
        simpa only [mem_closedBall, dist_eq_norm] using hx
      have h := hb.mapsTo hx'
      simpa only [mem_closedBall, dist_eq_norm, powMonoidHom_apply, Units.val_pow_eq_pow_val] using h
    · intro hu
      have hu' : (u : K) ∈ closedBall (1 : K) (‖(n : K)‖ * s) := by
        simpa only [mem_closedBall, dist_eq_norm] using hu
      obtain ⟨x, hx, hxu⟩ := hb.surjOn hu'
      have hxnorm : ‖x - 1‖ ≤ s := by simpa only [mem_closedBall, dist_eq_norm] using hx
      have hxone := normedField_norm_eq_one_of_sub_lt K (hxnorm.trans_lt (hsr.trans_lt hr1))
      have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (hxone ▸ one_ne_zero)
      refine ⟨Units.mk0 x hx0, hxnorm, ?_⟩
      apply Units.ext
      exact hxu
  · apply le_antisymm ?_ bot_le
    intro u hu
    apply Subgroup.mem_bot.mpr
    apply Units.ext
    apply hb.injOn
    · simpa only [mem_closedBall, dist_eq_norm] using hu.1
    · exact mem_closedBall_self hs0.le
    · have h := congrArg (fun v : Kˣ => (v : K)) hu.2
      simpa only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_one, one_pow] using h

end
end Dubon2026
