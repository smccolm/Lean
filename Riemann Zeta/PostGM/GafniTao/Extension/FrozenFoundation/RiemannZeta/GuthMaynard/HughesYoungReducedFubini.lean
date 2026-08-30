import RiemannZeta.GuthMaynard.HughesYoungReducedConsumer
import RiemannZeta.GuthMaynard.HughesYoungFubini

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff FourierTransform Interval Topology

noncomputable section

set_option maxHeartbeats 800000

namespace RiemannZeta.GuthMaynard

/-!
# Fubini bridge after gcd reduction
-/

/-- On the shifted surface, the reduced cleaned weight is literally the
original cleaned weight after dilating both physical coordinates, both box
scales, and the shift by the common divisor. -/
theorem hughesYoungReducedCleanedShiftWeight_eq_gcdScaled_cleaned
    (T c u X Y : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {r : ℤ} {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hshift : x - y = (r : ℝ)) :
    hughesYoungReducedCleanedShiftWeight T c u X Y h k r x y =
      hughesYoungCleanedShiftWeight T c u
        ((hughesYoungCommonDivisor h k : ℝ) * X)
        ((hughesYoungCommonDivisor h k : ℝ) * Y) h k
        ((hughesYoungCommonDivisor h k : ℤ) * r)
        ((hughesYoungCommonDivisor h k : ℝ) * x)
        ((hughesYoungCommonDivisor h k : ℝ) * y) := by
  let d : ℝ := hughesYoungCommonDivisor h k
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast hughesYoungCommonDivisor_pos hh
  have hdx : 0 < d * x := mul_pos hd hx
  have hdy : 0 < d * y := mul_pos hd hy
  have hshiftScaled :
      d * x - d * y = (((hughesYoungCommonDivisor h k : ℤ) * r : ℤ) : ℝ) := by
    rw [Int.cast_mul, Int.cast_natCast, ← hshift]
    dsimp only [d]
    ring
  rw [hughesYoungReducedCleanedShiftWeight_eq_heightIntegral
    T c u X Y hh hk hx hy hshift]
  rw [hughesYoungCleanedShiftWeight_eq_heightIntegral T c u
    ((hughesYoungCommonDivisor h k : ℝ) * X)
    ((hughesYoungCommonDivisor h k : ℝ) * Y) hh hk hdx hdy hshiftScaled]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  congr 1
  rw [← hughesYoungGCDScaledWeight_localized_eq_reduced
    T t c u X Y hh hk x y]
  rfl

/-- One reduced equation-(70) weight is continuous in its Mellin ordinate
on the exact shifted surface. -/
theorem continuous_hughesYoungReducedCleanedShiftWeight_ordinate
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (X Y : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {r : ℤ} {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hshift : x - y = (r : ℝ)) :
    Continuous (fun u : ℝ =>
      hughesYoungReducedCleanedShiftWeight T c u X Y h k r x y) := by
  rw [show (fun u : ℝ =>
      hughesYoungReducedCleanedShiftWeight T c u X Y h k r x y) =
      fun u : ℝ => hughesYoungCleanedShiftWeight T c u
        ((hughesYoungCommonDivisor h k : ℝ) * X)
        ((hughesYoungCommonDivisor h k : ℝ) * Y) h k
        ((hughesYoungCommonDivisor h k : ℤ) * r)
        ((hughesYoungCommonDivisor h k : ℝ) * x)
        ((hughesYoungCommonDivisor h k : ℝ) * y) by
    funext u
    exact hughesYoungReducedCleanedShiftWeight_eq_gcdScaled_cleaned
      T c u X Y hh hk hx hy hshift]
  let d : ℝ := hughesYoungCommonDivisor h k
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast hughesYoungCommonDivisor_pos hh
  have hshiftScaled :
      d * x - d * y = (((hughesYoungCommonDivisor h k : ℤ) * r : ℤ) : ℝ) := by
    rw [Int.cast_mul, Int.cast_natCast, ← hshift]
    dsimp only [d]
    ring
  exact continuous_hughesYoungCleanedShiftWeight_ordinate hT hc
    ((hughesYoungCommonDivisor h k : ℝ) * X)
    ((hughesYoungCommonDivisor h k : ℝ) * Y) hh hk
    (mul_pos hd hx) (mul_pos hd hy) hshiftScaled

/-- Localize the original integrated source on the pre-reduction dyadic box
and then dilate it into the coprime physical coordinates. -/
noncomputable def hughesYoungGCDReducedIntegratedBoxWeight
    (T c H X Y : ℝ) (h k : ℕ) (x y : ℝ) : ℂ :=
  let d : ℝ := hughesYoungCommonDivisor h k
  hughesYoungGCDScaledWeight h k
    (fun x' y' =>
      (hughesYoungDyadicCutoffAt (d * X) x' : ℂ) *
        (hughesYoungDyadicCutoffAt (d * Y) y' : ℂ) *
        hughesYoungIntegratedSourceWeight T c H h k x' y') x y

/-- The localized, gcd-dilated source is exactly the Mellin integral of the
reduced fixed-shift equation-(70) weight. -/
theorem hughesYoungGCDReducedIntegratedBoxWeight_eq_integral_reducedCleaned
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    (H X Y : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {r : ℤ} {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hshift : x - y = (r : ℝ)) :
    hughesYoungGCDReducedIntegratedBoxWeight T c H X Y h k x y =
      ∫ u in -H..H, (T : ℂ) *
        hughesYoungReducedCleanedShiftWeight T c u X Y h k r x y := by
  let d : ℝ := hughesYoungCommonDivisor h k
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast hughesYoungCommonDivisor_pos hh
  have hdx : 0 < d * x := mul_pos hd hx
  have hdy : 0 < d * y := mul_pos hd hy
  unfold hughesYoungGCDReducedIntegratedBoxWeight
  dsimp only [d]
  unfold hughesYoungGCDScaledWeight
  change (hughesYoungDyadicCutoffAt
        ((hughesYoungCommonDivisor h k : ℝ) * X)
        ((hughesYoungCommonDivisor h k : ℝ) * x) : ℂ) *
      (hughesYoungDyadicCutoffAt
        ((hughesYoungCommonDivisor h k : ℝ) * Y)
        ((hughesYoungCommonDivisor h k : ℝ) * y) : ℂ) *
      hughesYoungIntegratedSourceWeight T c H h k
        ((hughesYoungCommonDivisor h k : ℝ) * x)
        ((hughesYoungCommonDivisor h k : ℝ) * y) = _
  rw [dyadicCutoff_mul_hughesYoungIntegratedSourceWeight_eq_integral
    hT hc H ((hughesYoungCommonDivisor h k : ℝ) * X)
      ((hughesYoungCommonDivisor h k : ℝ) * Y) hh hk hdx hdy]
  apply intervalIntegral.integral_congr
  intro u _hu
  change (∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
      hughesYoungLocalizedMellinWeight T t c u
        ((hughesYoungCommonDivisor h k : ℝ) * X)
        ((hughesYoungCommonDivisor h k : ℝ) * Y) h k
        ((hughesYoungCommonDivisor h k : ℝ) * x)
        ((hughesYoungCommonDivisor h k : ℝ) * y)) =
    (T : ℂ) * hughesYoungReducedCleanedShiftWeight T c u X Y h k r x y
  rw [show (fun t : ℝ => (hughesYoungHeightWeight T t : ℂ) *
      hughesYoungLocalizedMellinWeight T t c u
        ((hughesYoungCommonDivisor h k : ℝ) * X)
        ((hughesYoungCommonDivisor h k : ℝ) * Y) h k
        ((hughesYoungCommonDivisor h k : ℝ) * x)
        ((hughesYoungCommonDivisor h k : ℝ) * y)) =
      fun t : ℝ => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungReducedLocalizedMellinWeight T t c u X Y h k x y by
    funext t
    rw [← hughesYoungGCDScaledWeight_localized_eq_reduced
      T t c u X Y hh hk x y]
    rfl]
  rw [hughesYoungReducedCleanedShiftWeight_eq_heightIntegral
    T c u X Y hh hk hx hy hshift]
  field_simp [hT.ne']

/-- Continuity in the Mellin ordinate of the exact reduced shifted-divisor
sum.  This is the finite-dimensional input needed to commute a finite shift
family with the compact ordinate integral. -/
theorem continuous_dfiDyadicShiftedDivisorSum_reducedCleaned_ordinate
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (X Y : ℝ)
    {h k a b M N : ℕ}
    (hh : 0 < h) (hk : 0 < k) (ha : 0 < a) (hb : 0 < b)
    (r : ℤ) :
    Continuous (fun u : ℝ =>
      dfiDyadicShiftedDivisorSum
        (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)
        a b M N r) := by
  exact continuous_finsetSum (Finset.Icc 1 M) fun m hm =>
    continuous_finsetSum (Finset.Icc 1 N) fun n hn => by
      by_cases hs : quadraticDivisorShift a b m n = r
      · simp only [hs, if_true]
        have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
        have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
        have hshift : (a * m : ℝ) - (b * n : ℝ) = (r : ℝ) := by
          unfold quadraticDivisorShift at hs
          exact_mod_cast hs
        exact (continuous_const.mul continuous_const).mul
          (continuous_hughesYoungReducedCleanedShiftWeight_ordinate
            hT hc X Y hh hk
            (by exact_mod_cast Nat.mul_pos ha hmpos)
            (by exact_mod_cast Nat.mul_pos hb hnpos) hshift)
      · simp only [hs, if_false]
        exact continuous_const

/-- One exact reduced shifted-divisor box from the opened AFE is the compact
Mellin integral of the corresponding reduced equation-(70) sum. -/
theorem dfiDyadicShiftedDivisorSum_gcdReducedIntegratedBox_eq_integral
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    (H X Y : ℝ) {h k a b M N : ℕ}
    (hh : 0 < h) (hk : 0 < k) (ha : 0 < a) (hb : 0 < b)
    (r : ℤ) :
    dfiDyadicShiftedDivisorSum
        (hughesYoungGCDReducedIntegratedBoxWeight T c H X Y h k)
        a b M N r =
      ∫ u in -H..H, (T : ℂ) *
        dfiDyadicShiftedDivisorSum
          (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)
          a b M N r := by
  let q : ℕ → ℕ → ℝ → ℂ := fun m n u =>
    if quadraticDivisorShift a b m n = r then
      divisorWeight m * divisorWeight n *
        ((T : ℂ) * hughesYoungReducedCleanedShiftWeight T c u X Y h k r
          (a * m) (b * n))
    else 0
  have hmpos : ∀ m ∈ Finset.Icc 1 M, 0 < m := by
    intro m hm
    exact (Finset.mem_Icc.mp hm).1
  have hnpos : ∀ n ∈ Finset.Icc 1 N, 0 < n := by
    intro n hn
    exact (Finset.mem_Icc.mp hn).1
  have hphysical : ∀ m ∈ Finset.Icc 1 M, ∀ n ∈ Finset.Icc 1 N,
      quadraticDivisorShift a b m n = r →
      (a * m : ℝ) - (b * n : ℝ) = (r : ℝ) := by
    intro m _hm n _hn hs
    unfold quadraticDivisorShift at hs
    exact_mod_cast hs
  have hq : ∀ m ∈ Finset.Icc 1 M, ∀ n ∈ Finset.Icc 1 N,
      Continuous (q m n) := by
    intro m hm n hn
    by_cases hs : quadraticDivisorShift a b m n = r
    · have hqeq : q m n = (fun u : ℝ =>
          divisorWeight m * divisorWeight n *
            ((T : ℂ) * hughesYoungReducedCleanedShiftWeight T c u X Y h k r
              (a * m) (b * n))) := by
        funext u
        simp [q, hs]
      rw [hqeq]
      exact (continuous_const.mul continuous_const).mul
        (continuous_const.mul
          (continuous_hughesYoungReducedCleanedShiftWeight_ordinate
            hT hc X Y hh hk
            (by exact_mod_cast Nat.mul_pos ha (hmpos m hm))
            (by exact_mod_cast Nat.mul_pos hb (hnpos n hn))
            (hphysical m hm n hn hs)))
    · have hqeq : q m n = (fun _u : ℝ => (0 : ℂ)) := by
        funext u
        simp [q, hs]
      rw [hqeq]
      exact continuous_const
  have hterm : ∀ m ∈ Finset.Icc 1 M, ∀ n ∈ Finset.Icc 1 N,
      (if quadraticDivisorShift a b m n = r then
        divisorWeight m * divisorWeight n *
          hughesYoungGCDReducedIntegratedBoxWeight T c H X Y h k
            (a * m) (b * n)
       else 0) = ∫ u in -H..H, q m n u := by
    intro m hm n hn
    by_cases hs : quadraticDivisorShift a b m n = r
    · simp only [hs, if_true]
      rw [hughesYoungGCDReducedIntegratedBoxWeight_eq_integral_reducedCleaned
        hT hc H X Y hh hk
        (by exact_mod_cast Nat.mul_pos ha (hmpos m hm))
        (by exact_mod_cast Nat.mul_pos hb (hnpos n hn))
        (hphysical m hm n hn hs)]
      have hqeq : q m n = (fun u : ℝ =>
          divisorWeight m * divisorWeight n *
            ((T : ℂ) * hughesYoungReducedCleanedShiftWeight T c u X Y h k r
              (a * m) (b * n))) := by
        funext u
        simp [q, hs]
      rw [hqeq]
      simp only [intervalIntegral.integral_const_mul]
    · simp [q, hs]
  have hswap :
      (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
        ∫ u in -H..H, q m n u) =
      ∫ u in -H..H, ∑ m ∈ Finset.Icc 1 M,
        ∑ n ∈ Finset.Icc 1 N, q m n u := by
    symm
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro m hm
      rw [intervalIntegral.integral_finsetSum]
      intro n hn
      exact (hq m hm n hn).intervalIntegrable _ _
    · intro m hm
      exact (continuous_finsetSum _ fun n hn => hq m hm n hn).intervalIntegrable _ _
  unfold dfiDyadicShiftedDivisorSum
  calc
    (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
      if quadraticDivisorShift a b m n = r then
        divisorWeight m * divisorWeight n *
          hughesYoungGCDReducedIntegratedBoxWeight T c H X Y h k
            (a * m) (b * n)
      else 0) =
        ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
          ∫ u in -H..H, q m n u := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      exact hterm m hm n hn
    _ = ∫ u in -H..H, ∑ m ∈ Finset.Icc 1 M,
        ∑ n ∈ Finset.Icc 1 N, q m n u := hswap
    _ = ∫ u in -H..H, (T : ℂ) *
        (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
          if quadraticDivisorShift a b m n = r then
            divisorWeight m * divisorWeight n *
              hughesYoungReducedCleanedShiftWeight T c u X Y h k r
                (a * m) (b * n)
          else 0) := by
      apply intervalIntegral.integral_congr
      intro u _hu
      dsimp only [q]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hs : quadraticDivisorShift a b m n = r
      · simp [hs]
        ring
      · simp [hs]

/-- Exact finite-family Fubini bridge for the gcd-reduced source. -/
theorem sum_dfiDyadicShiftedDivisorSum_gcdReducedIntegratedBox_eq_integral
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    (H X Y : ℝ) {h k a b M N : ℕ}
    (hh : 0 < h) (hk : 0 < k) (ha : 0 < a) (hb : 0 < b)
    (s : Finset ℤ) :
    (∑ r ∈ s, dfiDyadicShiftedDivisorSum
        (hughesYoungGCDReducedIntegratedBoxWeight T c H X Y h k)
        a b M N r) =
      ∫ u in -H..H, (T : ℂ) *
        (∑ r ∈ s, dfiDyadicShiftedDivisorSum
          (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)
          a b M N r) := by
  have hcontinuous : ∀ r : ℤ, Continuous (fun u : ℝ =>
      (T : ℂ) * dfiDyadicShiftedDivisorSum
        (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)
        a b M N r) := by
    intro r
    exact continuous_const.mul
      (continuous_dfiDyadicShiftedDivisorSum_reducedCleaned_ordinate
        hT hc X Y hh hk ha hb r)
  simp_rw [dfiDyadicShiftedDivisorSum_gcdReducedIntegratedBox_eq_integral
    hT hc H X Y hh hk ha hb]
  calc
    (∑ r ∈ s, ∫ u in -H..H, (T : ℂ) *
        dfiDyadicShiftedDivisorSum
          (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)
          a b M N r) =
        ∫ u in -H..H, ∑ r ∈ s, (T : ℂ) *
          dfiDyadicShiftedDivisorSum
            (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)
            a b M N r := by
      symm
      rw [intervalIntegral.integral_finsetSum]
      intro r hr
      exact (hcontinuous r).intervalIntegrable _ _
    _ = ∫ u in -H..H, (T : ℂ) *
        (∑ r ∈ s, dfiDyadicShiftedDivisorSum
          (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)
          a b M N r) := by
      apply intervalIntegral.integral_congr
      intro u _hu
      dsimp only
      exact (Finset.mul_sum s (fun r : ℤ =>
        dfiDyadicShiftedDivisorSum
          (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)
          a b M N r) (T : ℂ)).symm

end RiemannZeta.GuthMaynard
