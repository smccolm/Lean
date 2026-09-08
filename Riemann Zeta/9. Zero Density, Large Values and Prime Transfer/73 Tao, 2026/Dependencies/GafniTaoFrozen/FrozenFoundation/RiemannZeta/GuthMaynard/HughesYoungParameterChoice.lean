import Mathlib.Analysis.Complex.ExponentialBounds
import RiemannZeta.GuthMaynard.BetaDependence
import RiemannZeta.GuthMaynard.HughesYoungActiveDFIConsumer

open Filter Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Global Hughes--Young parameter choice

The physical AFE is truncated at `ceil (T^5)`.  One hundred logarithmic
dyadic generations cover that truncation together with the exact squared
Maynard--Pratt mollifier support.  These deliberately generous fixed powers
leave a large negative power in the opening-line remainder and avoid any
hidden dependence on the mollifier indices.
-/

/-- Polynomial physical cutoff used in the global fourth-moment assembly. -/
noncomputable def hughesYoungGlobalRadius (T : ℝ) : ℕ :=
  ⌈T ^ (5 : ℝ)⌉₊

/-- Logarithmic number of `sqrt 2` dyadic generations. -/
noncomputable def hughesYoungGlobalDepth (T : ℝ) : ℕ :=
  ⌈100 * Real.log T⌉₊

theorem hughesYoungGlobalRadius_pos {T : ℝ} (hT : 1 ≤ T) :
    0 < hughesYoungGlobalRadius T := by
  unfold hughesYoungGlobalRadius
  exact Nat.ceil_pos.mpr (by positivity)

theorem hughesYoungGlobalRadius_le {T : ℝ} (hT : 1 ≤ T) :
    (hughesYoungGlobalRadius T : ℝ) ≤ 2 * T ^ (5 : ℝ) := by
  have hpow : 1 ≤ T ^ (5 : ℝ) :=
    Real.one_le_rpow hT (by norm_num)
  have hc := Nat.ceil_lt_add_one (by positivity : 0 ≤ T ^ (5 : ℝ))
  dsimp [hughesYoungGlobalRadius]
  linarith

theorem thirty_lt_hundred_mul_log_hughesYoungDyadicRatio :
    30 < 100 * Real.log hughesYoungDyadicRatio := by
  unfold hughesYoungDyadicRatio
  rw [Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  linarith [Real.log_two_gt_d9]

theorem rpow_thirty_le_globalDepth {T : ℝ} (hT : 1 ≤ T) :
    T ^ (30 : ℝ) ≤
      hughesYoungDyadicRatio ^ (hughesYoungGlobalDepth T + 1) := by
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hthree : 30 ≤ 100 * Real.log hughesYoungDyadicRatio :=
    thirty_lt_hundred_mul_log_hughesYoungDyadicRatio.le
  have hfirst : T ^ (30 : ℝ) ≤
      T ^ (100 * Real.log hughesYoungDyadicRatio) :=
    Real.rpow_le_rpow_of_exponent_le hT hthree
  have hceil : 100 * Real.log T ≤ (hughesYoungGlobalDepth T : ℝ) := by
    exact Nat.le_ceil (100 * Real.log T)
  have hceil' : 100 * Real.log T ≤
      ((hughesYoungGlobalDepth T + 1 : ℕ) : ℝ) := by
    exact hceil.trans (by
      exact_mod_cast Nat.le_add_right (hughesYoungGlobalDepth T) 1)
  calc
    T ^ (30 : ℝ) ≤
        T ^ (100 * Real.log hughesYoungDyadicRatio) := hfirst
    _ = hughesYoungDyadicRatio ^ (100 * Real.log T) := by
      rw [Real.rpow_def_of_pos hughesYoungDyadicRatio_pos,
        Real.rpow_def_of_pos hT0]
      congr 1
      ring
    _ ≤ hughesYoungDyadicRatio ^
        (((hughesYoungGlobalDepth T + 1 : ℕ) : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le
        one_lt_hughesYoungDyadicRatio.le hceil'
    _ = hughesYoungDyadicRatio ^ (hughesYoungGlobalDepth T + 1) := by
      rw [Real.rpow_natCast]

theorem hughesYoungReducedLeft_le (h k : ℕ) :
    hughesYoungReducedLeft h k ≤ h := by
  rw [hughesYoungReducedLeft]
  exact Nat.div_le_self _ _

theorem hughesYoungReducedRight_le (h k : ℕ) :
    hughesYoungReducedRight h k ≤ k := by
  rw [hughesYoungReducedRight]
  exact Nat.div_le_self _ _

theorem oneHundredSixtyTwo_mul_rpow_nine_le_rpow_thirty
    {T : ℝ} (hT : 2 ≤ T) :
    (162 : ℝ) * T ^ (9 : ℝ) ≤ T ^ (30 : ℝ) := by
  have hpow : (162 : ℝ) ≤ T ^ (21 : ℝ) := by
    calc
      (162 : ℝ) ≤ 2 ^ (21 : ℕ) := by norm_num
      _ ≤ T ^ (21 : ℕ) := by gcongr
      _ = T ^ (21 : ℝ) := by simp
  rw [show T ^ (30 : ℝ) = T ^ (21 : ℝ) * T ^ (9 : ℝ) by
    rw [← Real.rpow_add (by positivity)]
    norm_num]
  gcongr

/-- The global parameter choice covers every pair of actual mollifier
indices in the exact finite source entry theorem. -/
theorem hughesYoungGlobal_cover {T : ℝ} (hT : 2 ≤ T)
    {h k : ℕ}
    (hh : h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2))
    (hk : k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2)) :
    ((((hughesYoungReducedLeft h k) *
      (hughesYoungReducedRight h k) * hughesYoungGlobalRadius T : ℕ) : ℝ)) ≤
        hughesYoungDyadicRatio ^ (hughesYoungGlobalDepth T + 1) := by
  have hT1 : 1 ≤ T := by linarith
  have hcut := detectorCutoff_le_three_mul T hT1
  have hrr := hughesYoungGlobalRadius_le hT1
  have hh' : (h : ℝ) ≤ (3 * T) ^ 2 := by
    have hhcast : (h : ℝ) ≤ ((detectorCutoff T : ℝ) ^ 2) := by
      exact_mod_cast (Finset.mem_Icc.mp hh).2
    exact hhcast.trans (pow_le_pow_left₀ (by positivity) hcut 2)
  have hk' : (k : ℝ) ≤ (3 * T) ^ 2 := by
    have hkcast : (k : ℝ) ≤ ((detectorCutoff T : ℝ) ^ 2) := by
      exact_mod_cast (Finset.mem_Icc.mp hk).2
    exact hkcast.trans (pow_le_pow_left₀ (by positivity) hcut 2)
  have ha : (hughesYoungReducedLeft h k : ℝ) ≤ h := by
    exact_mod_cast hughesYoungReducedLeft_le h k
  have hb : (hughesYoungReducedRight h k : ℝ) ≤ k := by
    exact_mod_cast hughesYoungReducedRight_le h k
  have hraw :
      ((hughesYoungReducedLeft h k : ℝ) *
        (hughesYoungReducedRight h k : ℝ) *
          (hughesYoungGlobalRadius T : ℝ)) ≤
            162 * T ^ (9 : ℝ) := by
    calc
      _ ≤ ((3 * T) ^ 2) * ((3 * T) ^ 2) *
          (2 * T ^ (5 : ℝ)) := by
        gcongr
        · exact ha.trans hh'
        · exact hb.trans hk'
      _ = 162 * T ^ (9 : ℝ) := by
        simp only [Real.rpow_ofNat]
        ring
  simp only [Nat.cast_mul]
  exact hraw.trans
    ((oneHundredSixtyTwo_mul_rpow_nine_le_rpow_thirty hT).trans
      (rpow_thirty_le_globalDepth hT1))

end RiemannZeta.GuthMaynard
