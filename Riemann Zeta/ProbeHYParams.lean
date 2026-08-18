import RiemannZeta.GuthMaynard.HughesYoungActiveDFIConsumer
import RiemannZeta.GuthMaynard.BetaDependence
import Mathlib.Analysis.Complex.ExponentialBounds

open Filter Topology

#check Nat.le_ceil
#check Nat.ceil_lt_add_one
#check Real.rpow_natCast
#check Real.rpow_add
#check Real.rpow_mul
#check Real.rpow_le_rpow_of_exponent_le
#check Real.log_sqrt
#check Real.log_two_gt_d9
#check tendsto_rpow_atTop

open RiemannZeta.GuthMaynard

noncomputable def rr (T : ℝ) : ℕ := ⌈T ^ (5 : ℝ)⌉₊
noncomputable def kk (T : ℝ) : ℕ := ⌈100 * Real.log T⌉₊

example {T : ℝ} (hT : 1 ≤ T) :
    (rr T : ℝ) ≤ 2 * T ^ (5 : ℝ) := by
  have hpow : 1 ≤ T ^ (5 : ℝ) :=
    Real.one_le_rpow hT (by norm_num)
  have hc := Nat.ceil_lt_add_one (by positivity : 0 ≤ T ^ (5 : ℝ))
  dsimp [rr]
  linarith

example : 30 < 100 * Real.log hughesYoungDyadicRatio := by
  unfold hughesYoungDyadicRatio
  rw [Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  linarith [Real.log_two_gt_d9]

example {T : ℝ} (hT : 0 < T) :
    hughesYoungDyadicRatio ^ (100 * Real.log T) =
      T ^ (100 * Real.log hughesYoungDyadicRatio) := by
  have hr : 0 < hughesYoungDyadicRatio := hughesYoungDyadicRatio_pos
  rw [Real.rpow_def_of_pos hr, Real.rpow_def_of_pos hT]
  congr 1
  ring

example {T : ℝ} (hT : 1 ≤ T) :
    T ^ (30 : ℝ) ≤ hughesYoungDyadicRatio ^ (kk T + 1) := by
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hr1 : 1 < hughesYoungDyadicRatio := one_lt_hughesYoungDyadicRatio
  have hthree : 30 ≤ 100 * Real.log hughesYoungDyadicRatio :=
    (show 30 < 100 * Real.log hughesYoungDyadicRatio by
      unfold hughesYoungDyadicRatio
      rw [Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      linarith [Real.log_two_gt_d9]).le
  have hfirst : T ^ (30 : ℝ) ≤
      T ^ (100 * Real.log hughesYoungDyadicRatio) :=
    Real.rpow_le_rpow_of_exponent_le hT hthree
  have hceil : 100 * Real.log T ≤ (kk T : ℝ) := by
    exact Nat.le_ceil (100 * Real.log T)
  have hceil' : 100 * Real.log T ≤ ((kk T + 1 : ℕ) : ℝ) := by
    exact hceil.trans (by exact_mod_cast Nat.le_add_right (kk T) 1)
  have hsecond : hughesYoungDyadicRatio ^ (100 * Real.log T) ≤
      hughesYoungDyadicRatio ^ (((kk T + 1 : ℕ) : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hr1.le hceil'
  calc
    T ^ (30 : ℝ) ≤ T ^ (100 * Real.log hughesYoungDyadicRatio) := hfirst
    _ = hughesYoungDyadicRatio ^ (100 * Real.log T) := by
      rw [show hughesYoungDyadicRatio ^ (100 * Real.log T) =
          T ^ (100 * Real.log hughesYoungDyadicRatio) by
        rw [Real.rpow_def_of_pos hughesYoungDyadicRatio_pos,
          Real.rpow_def_of_pos hT0]
        congr 1
        ring]
    _ ≤ hughesYoungDyadicRatio ^ (((kk T + 1 : ℕ) : ℝ)) := hsecond
    _ = hughesYoungDyadicRatio ^ (kk T + 1) := by
      rw [Real.rpow_natCast]

example {h k : ℕ} : hughesYoungReducedLeft h k ≤ h := by
  rw [hughesYoungReducedLeft]
  exact Nat.div_le_self _ _

example {h k : ℕ} : hughesYoungReducedRight h k ≤ k := by
  rw [hughesYoungReducedRight]
  exact Nat.div_le_self _ _

example {T : ℝ} (hT : 2 ≤ T) :
    (162 : ℝ) * T ^ (9 : ℝ) ≤ T ^ (30 : ℝ) := by
  have hpow : (162 : ℝ) ≤ T ^ (21 : ℝ) := by
    calc
      (162 : ℝ) ≤ 2 ^ (21 : ℕ) := by norm_num
      _ ≤ T ^ (21 : ℕ) := by gcongr
      _ = T ^ (21 : ℝ) := by simp
  rw [show T ^ (30 : ℝ) = T ^ (21 : ℝ) * T ^ (9 : ℝ) by
    rw [← Real.rpow_add (by positivity)]; norm_num]
  gcongr

example {T : ℝ} (hT : 2 ≤ T)
    {h k : ℕ}
    (hh : h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2))
    (hk : k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2)) :
    ((((hughesYoungReducedLeft h k) *
      (hughesYoungReducedRight h k) * rr T : ℕ) : ℝ)) ≤
        hughesYoungDyadicRatio ^ (kk T + 1) := by
  have hT1 : 1 ≤ T := by linarith
  have hcut := detectorCutoff_le_three_mul T hT1
  have hrr : (rr T : ℝ) ≤ 2 * T ^ (5 : ℝ) := by
    have hpow : 1 ≤ T ^ (5 : ℝ) := Real.one_le_rpow hT1 (by norm_num)
    have hc := Nat.ceil_lt_add_one (by positivity : 0 ≤ T ^ (5 : ℝ))
    dsimp [rr]
    linarith
  have hh' : (h : ℝ) ≤ (3 * T) ^ 2 := by
    have hhcast : (h : ℝ) ≤ ((detectorCutoff T : ℝ) ^ 2) := by
      exact_mod_cast (Finset.mem_Icc.mp hh).2
    exact hhcast.trans (pow_le_pow_left₀ (by positivity) hcut 2)
  have hk' : (k : ℝ) ≤ (3 * T) ^ 2 := by
    have hkcast : (k : ℝ) ≤ ((detectorCutoff T : ℝ) ^ 2) := by
      exact_mod_cast (Finset.mem_Icc.mp hk).2
    exact hkcast.trans (pow_le_pow_left₀ (by positivity) hcut 2)
  have ha : (hughesYoungReducedLeft h k : ℝ) ≤ h := by
    exact_mod_cast (show hughesYoungReducedLeft h k ≤ h by
      rw [hughesYoungReducedLeft]; exact Nat.div_le_self _ _)
  have hb : (hughesYoungReducedRight h k : ℝ) ≤ k := by
    exact_mod_cast (show hughesYoungReducedRight h k ≤ k by
      rw [hughesYoungReducedRight]; exact Nat.div_le_self _ _)
  have hraw :
      ((hughesYoungReducedLeft h k : ℝ) *
        (hughesYoungReducedRight h k : ℝ) * (rr T : ℝ)) ≤
          162 * T ^ (9 : ℝ) := by
    calc
      _ ≤ ((3 * T) ^ 2) * ((3 * T) ^ 2) * (2 * T ^ (5 : ℝ)) := by
        gcongr
        · exact ha.trans hh'
        · exact hb.trans hk'
      _ = 162 * T ^ (9 : ℝ) := by
        simp only [Real.rpow_ofNat]
        ring
  simp only [Nat.cast_mul]
  exact hraw.trans ((show (162 : ℝ) * T ^ (9 : ℝ) ≤ T ^ (30 : ℝ) by
    have hpow : (162 : ℝ) ≤ T ^ (21 : ℝ) := by
      calc
        (162 : ℝ) ≤ 2 ^ (21 : ℕ) := by norm_num
        _ ≤ T ^ (21 : ℕ) := by gcongr
        _ = T ^ (21 : ℝ) := by simp
    rw [show T ^ (30 : ℝ) = T ^ (21 : ℝ) * T ^ (9 : ℝ) by
      rw [← Real.rpow_add (by positivity)]; norm_num]
    gcongr).trans (show T ^ (30 : ℝ) ≤
      hughesYoungDyadicRatio ^ (kk T + 1) by
    have hT0 : 0 < T := by positivity
    have hr1 : 1 < hughesYoungDyadicRatio := one_lt_hughesYoungDyadicRatio
    have hthree : 30 ≤ 100 * Real.log hughesYoungDyadicRatio := by
      have : 30 < 100 * Real.log hughesYoungDyadicRatio := by
        unfold hughesYoungDyadicRatio
        rw [Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        linarith [Real.log_two_gt_d9]
      exact this.le
    have hfirst := Real.rpow_le_rpow_of_exponent_le hT1 hthree
    have hceil : 100 * Real.log T ≤ (kk T : ℝ) := Nat.le_ceil _
    have hceil' : 100 * Real.log T ≤ ((kk T + 1 : ℕ) : ℝ) :=
      hceil.trans (by exact_mod_cast Nat.le_add_right (kk T) 1)
    calc
      T ^ (30 : ℝ) ≤ T ^ (100 * Real.log hughesYoungDyadicRatio) := hfirst
      _ = hughesYoungDyadicRatio ^ (100 * Real.log T) := by
        rw [Real.rpow_def_of_pos hughesYoungDyadicRatio_pos,
          Real.rpow_def_of_pos hT0]
        congr 1
        ring
      _ ≤ hughesYoungDyadicRatio ^ (((kk T + 1 : ℕ) : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hr1.le hceil'
      _ = _ := by rw [Real.rpow_natCast]))
