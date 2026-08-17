import RiemannZeta.GuthMaynard.HughesYoungDyadicAssembly

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff FourierTransform Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Isolated lower-endpoint terms in the Hughes--Young partition

The smooth dyadic partition is zero at the integer endpoint `1`.  The
endpoint is therefore treated separately.  Centering an auxiliary smooth
box at each positive source point gives an exact value-one localizer and
allows the same height Fourier transform to be used without changing the
source term.
-/

/-- Exact Mellin/Fourier representation of the unlocalized integrated source
weight at one positive physical point. -/
theorem hughesYoungIntegratedSourceWeight_eq_centered_cleaned
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (H : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {r : ℤ} {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hshift : x - y = (r : ℝ)) :
    hughesYoungIntegratedSourceWeight T c H h k x y =
      ∫ u in -H..H, (T : ℂ) *
        hughesYoungCleanedShiftWeight T c u
          (x / hughesYoungDyadicRatio) (y / hughesYoungDyadicRatio)
          h k r x y := by
  have hleft := hughesYoungDyadicCutoffAt_eq_one_centered hx
  have hright := hughesYoungDyadicCutoffAt_eq_one_centered hy
  have hraw := dyadicCutoff_mul_hughesYoungIntegratedSourceWeight_eq_cleaned
    hT hc H (x / hughesYoungDyadicRatio) (y / hughesYoungDyadicRatio)
      hh hk hx hy hshift
  simpa [hleft, hright] using hraw

/-- The centered representation with the harmless `T` normalization
cancelled exposes exactly the height Fourier transform at `log(y/x)`. -/
theorem hughesYoungIntegratedSourceWeight_eq_centered_transform
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (H : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {r : ℤ} {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hshift : x - y = (r : ℝ)) :
    hughesYoungIntegratedSourceWeight T c H h k x y =
      ∫ u in -H..H,
        hughesYoungLocalizedStaticWeight T c u
          (x / hughesYoungDyadicRatio) (y / hughesYoungDyadicRatio)
          h k x y *
        hughesYoungHeightTransform T c u (Real.log (y / x)) := by
  rw [hughesYoungIntegratedSourceWeight_eq_centered_cleaned
    hT hc H hh hk hx hy hshift]
  apply intervalIntegral.integral_congr
  intro u _hu
  change (T : ℂ) *
      hughesYoungCleanedShiftWeight T c u
        (x / hughesYoungDyadicRatio) (y / hughesYoungDyadicRatio)
        h k r x y =
    hughesYoungLocalizedStaticWeight T c u
        (x / hughesYoungDyadicRatio) (y / hughesYoungDyadicRatio)
        h k x y *
      hughesYoungHeightTransform T c u (Real.log (y / x))
  rw [hughesYoungCleanedShiftWeight_eq_transform_source
    T c u (x / hughesYoungDyadicRatio) (y / hughesYoungDyadicRatio)
      hx hy hshift]
  field_simp [hT.ne']

/-- The isolated lower endpoint is itself an ordinary smooth dyadic box if
the grid is started one ratio earlier.  This identity holds on every
positive integral reduced coordinate, which is exactly the arithmetic
lattice on which the finite quadratic-divisor sum is evaluated. -/
theorem hughesYoungDyadicStep_nat_eq_initialCutoff
    {n : ℕ} (hn : 0 < n) :
    hughesYoungDyadicStep (n : ℝ) =
      hughesYoungDyadicCutoffAt
        (1 / hughesYoungDyadicRatio) (n : ℝ) := by
  by_cases hone : n = 1
  · subst n
    rw [hughesYoungDyadicStep_eq_one (by norm_num)]
    symm
    simpa using hughesYoungDyadicCutoffAt_eq_one_centered
      (show (0 : ℝ) < 1 by norm_num)
  · have hn2 : 2 ≤ n := by omega
    rw [hughesYoungDyadicStep_nat_eq_zero_of_two_le hn2]
    unfold hughesYoungDyadicCutoffAt
    apply (hughesYoungDyadicCutoff_eq_zero_of_two_le ?_).symm
    have hq1 : 1 ≤ hughesYoungDyadicRatio :=
      one_lt_hughesYoungDyadicRatio.le
    have hn2R : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hq0 : 0 < hughesYoungDyadicRatio := hughesYoungDyadicRatio_pos
    calc
      (2 : ℝ) ≤ n := hn2R
      _ ≤ (n : ℝ) * hughesYoungDyadicRatio := by nlinarith
      _ = (n : ℝ) / (1 / hughesYoungDyadicRatio) := by
        field_simp [hq0.ne']

/-- Positive common dilation does not change the reduced dyadic coordinate. -/
theorem hughesYoungDyadicCutoffAt_mul_cancel
    {d X x : ℝ} (hd : 0 < d) :
    hughesYoungDyadicCutoffAt (d * X) (d * x) =
      hughesYoungDyadicCutoffAt X x := by
  unfold hughesYoungDyadicCutoffAt
  congr 1
  field_simp [hd.ne']

/-- A nonzero smooth dyadic cutoff lies strictly above its lower endpoint. -/
theorem lt_of_hughesYoungDyadicCutoffAt_ne_zero
    {X x : ℝ} (hX : 0 < X)
    (hne : hughesYoungDyadicCutoffAt X x ≠ 0) :
    X < x := by
  by_contra hnot
  apply hne
  unfold hughesYoungDyadicCutoffAt
  apply hughesYoungDyadicCutoff_eq_zero_of_le_one
  exact (div_le_one hX).2 (le_of_not_gt hnot)

/-- A zero reduced left cutoff kills the exact gcd-scaled integrated source
weight. -/
theorem hughesYoungGCDReducedIntegratedBoxWeight_eq_zero_of_leftCutoff
    (T c H X Y : ℝ) {h k : ℕ} (hh : 0 < h) {x y : ℝ}
    (hzero : hughesYoungDyadicCutoffAt X x = 0) :
    hughesYoungGCDReducedIntegratedBoxWeight T c H X Y h k x y = 0 := by
  have hd : (0 : ℝ) < hughesYoungCommonDivisor h k := by
    exact_mod_cast hughesYoungCommonDivisor_pos hh
  unfold hughesYoungGCDReducedIntegratedBoxWeight hughesYoungGCDScaledWeight
  dsimp only
  rw [hughesYoungDyadicCutoffAt_mul_cancel hd, hzero]
  norm_num

/-- Symmetric vanishing from the reduced right cutoff. -/
theorem hughesYoungGCDReducedIntegratedBoxWeight_eq_zero_of_rightCutoff
    (T c H X Y : ℝ) {h k : ℕ} (hh : 0 < h) {x y : ℝ}
    (hzero : hughesYoungDyadicCutoffAt Y y = 0) :
    hughesYoungGCDReducedIntegratedBoxWeight T c H X Y h k x y = 0 := by
  have hd : (0 : ℝ) < hughesYoungCommonDivisor h k := by
    exact_mod_cast hughesYoungCommonDivisor_pos hh
  unfold hughesYoungGCDReducedIntegratedBoxWeight hughesYoungGCDScaledWeight
  dsimp only
  rw [show hughesYoungDyadicCutoffAt
      ((hughesYoungCommonDivisor h k : ℝ) * Y)
      ((hughesYoungCommonDivisor h k : ℝ) * y) =
      hughesYoungDyadicCutoffAt Y y from
        hughesYoungDyadicCutoffAt_mul_cancel hd, hzero]
  norm_num

/-- The gcd-scaled boundary cutoff in the left source coordinate agrees on
the full positive arithmetic lattice with the initial smooth box at reduced
scale `1 / sqrt 2`. -/
theorem hughesYoungGCDBoundaryCutoff_eq_initialCutoff_left_nat
    {h k m : ℕ} (hh : 0 < h) (hm : 0 < m) :
    hughesYoungGCDBoundaryCutoff h k (((h * m : ℕ) : ℝ)) =
      hughesYoungDyadicCutoffAt
        (hughesYoungCommonDivisor h k / hughesYoungDyadicRatio)
        (((h * m : ℕ) : ℝ)) := by
  have hd : (0 : ℝ) < hughesYoungCommonDivisor h k := by
    exact_mod_cast hughesYoungCommonDivisor_pos hh
  have ha : 0 < hughesYoungReducedLeft h k :=
    hughesYoungReducedLeft_pos (k := k) hh
  have ham : 0 < hughesYoungReducedLeft h k * m := Nat.mul_pos ha hm
  have hscale : (((h * m : ℕ) : ℝ) / hughesYoungCommonDivisor h k) =
      (((hughesYoungReducedLeft h k * m : ℕ) : ℝ)) := by
    have hfactor := hughesYoungCommonDivisor_mul_reducedLeft h k
    have hfactorR : (h : ℝ) =
        (hughesYoungCommonDivisor h k : ℝ) *
          (hughesYoungReducedLeft h k : ℝ) := by
      exact_mod_cast hfactor.symm
    push_cast
    rw [hfactorR]
    field_simp [hd.ne']
  have hcut :
      hughesYoungDyadicCutoffAt
          (hughesYoungCommonDivisor h k / hughesYoungDyadicRatio)
          (((h * m : ℕ) : ℝ)) =
        hughesYoungDyadicCutoffAt
          (1 / hughesYoungDyadicRatio)
          (((hughesYoungReducedLeft h k * m : ℕ) : ℝ)) := by
    unfold hughesYoungDyadicCutoffAt
    congr 1
    calc
      ((h * m : ℕ) : ℝ) /
          ((hughesYoungCommonDivisor h k : ℝ) /
            hughesYoungDyadicRatio) =
          (((h * m : ℕ) : ℝ) /
            hughesYoungCommonDivisor h k) * hughesYoungDyadicRatio := by
              field_simp [hd.ne', hughesYoungDyadicRatio_pos.ne']
      _ = ((hughesYoungReducedLeft h k * m : ℕ) : ℝ) *
          hughesYoungDyadicRatio := by rw [hscale]
      _ = ((hughesYoungReducedLeft h k * m : ℕ) : ℝ) /
          (1 / hughesYoungDyadicRatio) := by
            field_simp [hughesYoungDyadicRatio_pos.ne']
  unfold hughesYoungGCDBoundaryCutoff
  rw [hscale, hcut]
  exact hughesYoungDyadicStep_nat_eq_initialCutoff ham

/-- Right-coordinate version of the initial smooth-box identity. -/
theorem hughesYoungGCDBoundaryCutoff_eq_initialCutoff_right_nat
    {h k n : ℕ} (hh : 0 < h) (hk : 0 < k) (hn : 0 < n) :
    hughesYoungGCDBoundaryCutoff h k (((k * n : ℕ) : ℝ)) =
      hughesYoungDyadicCutoffAt
        (hughesYoungCommonDivisor h k / hughesYoungDyadicRatio)
        (((k * n : ℕ) : ℝ)) := by
  have hd : (0 : ℝ) < hughesYoungCommonDivisor h k := by
    exact_mod_cast hughesYoungCommonDivisor_pos hh
  have hb : 0 < hughesYoungReducedRight h k :=
    hughesYoungReducedRight_pos hh hk
  have hbn : 0 < hughesYoungReducedRight h k * n := Nat.mul_pos hb hn
  have hscale : (((k * n : ℕ) : ℝ) / hughesYoungCommonDivisor h k) =
      (((hughesYoungReducedRight h k * n : ℕ) : ℝ)) := by
    have hfactor := hughesYoungCommonDivisor_mul_reducedRight h k
    have hfactorR : (k : ℝ) =
        (hughesYoungCommonDivisor h k : ℝ) *
          (hughesYoungReducedRight h k : ℝ) := by
      exact_mod_cast hfactor.symm
    push_cast
    rw [hfactorR]
    field_simp [hd.ne']
  have hcut :
      hughesYoungDyadicCutoffAt
          (hughesYoungCommonDivisor h k / hughesYoungDyadicRatio)
          (((k * n : ℕ) : ℝ)) =
        hughesYoungDyadicCutoffAt
          (1 / hughesYoungDyadicRatio)
          (((hughesYoungReducedRight h k * n : ℕ) : ℝ)) := by
    unfold hughesYoungDyadicCutoffAt
    congr 1
    calc
      ((k * n : ℕ) : ℝ) /
          ((hughesYoungCommonDivisor h k : ℝ) /
            hughesYoungDyadicRatio) =
          (((k * n : ℕ) : ℝ) /
            hughesYoungCommonDivisor h k) * hughesYoungDyadicRatio := by
              field_simp [hd.ne', hughesYoungDyadicRatio_pos.ne']
      _ = ((hughesYoungReducedRight h k * n : ℕ) : ℝ) *
          hughesYoungDyadicRatio := by rw [hscale]
      _ = ((hughesYoungReducedRight h k * n : ℕ) : ℝ) /
          (1 / hughesYoungDyadicRatio) := by
            field_simp [hughesYoungDyadicRatio_pos.ne']
  unfold hughesYoungGCDBoundaryCutoff
  rw [hscale, hcut]
  exact hughesYoungDyadicStep_nat_eq_initialCutoff hbn

/-- The left mixed boundary piece is definitionally the first ordinary
localized Hughes--Young box after the lattice cutoff identity is inserted. -/
theorem finiteQuadraticDivisorOffDiagonalPiece_boundary_left_eq_initialBox
    (T c H Y : ℝ) {h k M N : ℕ} (hh : 0 < h) :
    finiteQuadraticDivisorOffDiagonalPiece h k M N
        (hughesYoungIntegratedSourceWeight T c H h k)
        (hughesYoungGCDBoundaryCutoff h k)
        (hughesYoungDyadicCutoffAt
          (hughesYoungCommonDivisor h k * Y)) =
      hughesYoungLocalizedOffDiagonalBox T c H
        (1 / hughesYoungDyadicRatio) Y h k M N := by
  classical
  unfold finiteQuadraticDivisorOffDiagonalPiece
    hughesYoungLocalizedOffDiagonalBox
    hughesYoungPreReducedIntegratedBoxWeight
    finiteQuadraticDivisorOffDiagonal
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  have hm0 : 0 < m := (Finset.mem_Icc.mp hm).1
  dsimp only
  rw [hughesYoungGCDBoundaryCutoff_eq_initialCutoff_left_nat hh hm0]
  have hscale :
      (hughesYoungCommonDivisor h k : ℝ) /
          hughesYoungDyadicRatio =
        hughesYoungCommonDivisor h k *
          (1 / hughesYoungDyadicRatio) := by ring
  rw [hscale]

/-- The right mixed boundary piece is the symmetric initial localized box. -/
theorem finiteQuadraticDivisorOffDiagonalPiece_boundary_right_eq_initialBox
    (T c H X : ℝ) {h k M N : ℕ} (hh : 0 < h) (hk : 0 < k) :
    finiteQuadraticDivisorOffDiagonalPiece h k M N
        (hughesYoungIntegratedSourceWeight T c H h k)
        (hughesYoungDyadicCutoffAt
          (hughesYoungCommonDivisor h k * X))
        (hughesYoungGCDBoundaryCutoff h k) =
      hughesYoungLocalizedOffDiagonalBox T c H
        X (1 / hughesYoungDyadicRatio) h k M N := by
  classical
  unfold finiteQuadraticDivisorOffDiagonalPiece
    hughesYoungLocalizedOffDiagonalBox
    hughesYoungPreReducedIntegratedBoxWeight
    finiteQuadraticDivisorOffDiagonal
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : 0 < n := (Finset.mem_Icc.mp hn).1
  dsimp only
  rw [hughesYoungGCDBoundaryCutoff_eq_initialCutoff_right_nat hh hk hn0]
  have hscale :
      (hughesYoungCommonDivisor h k : ℝ) /
          hughesYoungDyadicRatio =
        hughesYoungCommonDivisor h k *
          (1 / hughesYoungDyadicRatio) := by ring
  rw [hscale]

/-- On the first smooth box, every positive integral left coordinate other
than `1` is killed exactly by the cutoff. -/
theorem hughesYoungGCDReducedIntegratedBoxWeight_initial_left_eq_zero
    (T c H Y : ℝ) {h k x : ℕ} (hh : 0 < h) (hx : 2 ≤ x) (y : ℝ) :
    hughesYoungGCDReducedIntegratedBoxWeight T c H
        (1 / hughesYoungDyadicRatio) Y h k x y = 0 := by
  have hd : (0 : ℝ) < hughesYoungCommonDivisor h k := by
    exact_mod_cast hughesYoungCommonDivisor_pos hh
  have hstep := hughesYoungDyadicStep_nat_eq_initialCutoff
    (show 0 < x by omega)
  have hzero : hughesYoungDyadicCutoffAt
      (1 / hughesYoungDyadicRatio) (x : ℝ) = 0 := by
    rw [← hstep]
    exact hughesYoungDyadicStep_nat_eq_zero_of_two_le hx
  unfold hughesYoungGCDReducedIntegratedBoxWeight hughesYoungGCDScaledWeight
  dsimp only
  rw [show hughesYoungDyadicCutoffAt
      ((hughesYoungCommonDivisor h k : ℝ) *
        (1 / hughesYoungDyadicRatio))
      ((hughesYoungCommonDivisor h k : ℝ) * (x : ℝ)) =
      hughesYoungDyadicCutoffAt (1 / hughesYoungDyadicRatio) (x : ℝ) from
        hughesYoungDyadicCutoffAt_mul_cancel hd, hzero]
  norm_num

/-- Symmetric vanishing on the first smooth right box. -/
theorem hughesYoungGCDReducedIntegratedBoxWeight_initial_right_eq_zero
    (T c H X : ℝ) {h k y : ℕ} (hh : 0 < h) (hy : 2 ≤ y) (x : ℝ) :
    hughesYoungGCDReducedIntegratedBoxWeight T c H X
        (1 / hughesYoungDyadicRatio) h k x y = 0 := by
  have hd : (0 : ℝ) < hughesYoungCommonDivisor h k := by
    exact_mod_cast hughesYoungCommonDivisor_pos hh
  have hstep := hughesYoungDyadicStep_nat_eq_initialCutoff
    (show 0 < y by omega)
  have hzero : hughesYoungDyadicCutoffAt
      (1 / hughesYoungDyadicRatio) (y : ℝ) = 0 := by
    rw [← hstep]
    exact hughesYoungDyadicStep_nat_eq_zero_of_two_le hy
  unfold hughesYoungGCDReducedIntegratedBoxWeight hughesYoungGCDScaledWeight
  dsimp only
  rw [show hughesYoungDyadicCutoffAt
      ((hughesYoungCommonDivisor h k : ℝ) *
        (1 / hughesYoungDyadicRatio))
      ((hughesYoungCommonDivisor h k : ℝ) * (y : ℝ)) =
      hughesYoungDyadicCutoffAt (1 / hughesYoungDyadicRatio) (y : ℝ) from
        hughesYoungDyadicCutoffAt_mul_cancel hd, hzero]
  norm_num

end RiemannZeta.GuthMaynard
