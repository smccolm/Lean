import RiemannZeta.GuthMaynard.HughesYoungInfiniteBox
import RiemannZeta.GuthMaynard.HughesYoungBoundaryBound

open Complex Finset Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff FourierTransform Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Canonical finite realizations of the infinite Hughes--Young boxes

This file discharges the elementary scale hypotheses between the locally
finite partition in equation (69) and the finite DFI consumer.  A regular
box either meets the positive arithmetic lattice and hence satisfies all
DFI endpoint hypotheses, or its cutoff is identically zero on that lattice.
-/

theorem one_le_hughesYoungFullDyadicScale_succ (i : ℕ) :
    1 ≤ hughesYoungFullDyadicScale (i + 1) := by
  exact one_le_hughesYoungDyadicScale i

theorem two_mul_fullDyadicScale_div_le_bound
    {a i : ℕ} (ha : 0 < a) :
    2 * hughesYoungFullDyadicScale i / (a : ℝ) ≤
      (hughesYoungFullDyadicBound i : ℝ) := by
  have haOne : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hscale : 0 ≤ 2 * hughesYoungFullDyadicScale i :=
    mul_nonneg (by norm_num) (hughesYoungFullDyadicScale_pos i).le
  calc
    2 * hughesYoungFullDyadicScale i / (a : ℝ) ≤
        2 * hughesYoungFullDyadicScale i := by
      exact (div_le_self hscale haOne)
    _ ≤ (hughesYoungFullDyadicBound i : ℝ) :=
      two_mul_hughesYoungFullDyadicScale_le_bound i

theorem hughesYoungFullDyadicCutoff_eq_zero_of_two_scale_lt
    {a m i : ℕ} (hm : 0 < m)
    (hlarge : 2 * hughesYoungFullDyadicScale i < (a : ℝ)) :
    hughesYoungFullDyadicCutoff i ((a * m : ℕ) : ℝ) = 0 := by
  by_contra hne
  have hsupp := support_hughesYoungDyadicCutoffAt_subset
    (hughesYoungFullDyadicScale_pos i) hne
  have hmOne : 1 ≤ m := hm
  have ham : a ≤ a * m := by
    simpa only [mul_one] using Nat.mul_le_mul_left a hmOne
  have hamReal : (a : ℝ) ≤ ((a * m : ℕ) : ℝ) := by exact_mod_cast ham
  linarith [hsupp.2]

theorem hughesYoungLocalizedOffDiagonalBox_eq_zero_of_left_scale
    (T c H : ℝ) {X Y : ℝ} {h k M N : ℕ}
    (hX : 0 < X) (hh : 0 < h)
    (hlarge : 2 * X < (hughesYoungReducedLeft h k : ℝ)) :
    hughesYoungLocalizedOffDiagonalBox T c H X Y h k M N = 0 := by
  unfold hughesYoungLocalizedOffDiagonalBox
    finiteQuadraticDivisorOffDiagonal
  apply Finset.sum_eq_zero
  intro m hm
  apply Finset.sum_eq_zero
  intro n hn
  by_cases hs : quadraticDivisorShift h k m n = 0
  · simp [hs]
  · simp only [hs, if_false]
    have hmPos : 0 < m := by
      have := (Finset.mem_Icc.mp hm).1
      omega
    have hd : (0 : ℝ) < hughesYoungCommonDivisor h k := by
      exact_mod_cast hughesYoungCommonDivisor_pos hh
    have hfactor : (h : ℝ) =
        (hughesYoungCommonDivisor h k : ℝ) *
          (hughesYoungReducedLeft h k : ℝ) := by
      exact_mod_cast (hughesYoungCommonDivisor_mul_reducedLeft h k).symm
    have hcut : hughesYoungDyadicCutoffAt
        ((hughesYoungCommonDivisor h k : ℝ) * X)
        ((h * m : ℕ) : ℝ) = 0 := by
      by_contra hne
      have hsupp := support_hughesYoungDyadicCutoffAt_subset
        (mul_pos hd hX) hne
      have hmOne : 1 ≤ m := hmPos
      have hredMul : hughesYoungReducedLeft h k ≤
          hughesYoungReducedLeft h k * m := by
        simpa only [mul_one] using
          Nat.mul_le_mul_left (hughesYoungReducedLeft h k) hmOne
      have hredMulReal : (hughesYoungReducedLeft h k : ℝ) ≤
          ((hughesYoungReducedLeft h k * m : ℕ) : ℝ) := by
        exact_mod_cast hredMul
      have hmul :
          (hughesYoungCommonDivisor h k : ℝ) *
              (hughesYoungReducedLeft h k : ℝ) ≤
            (hughesYoungCommonDivisor h k : ℝ) *
              ((hughesYoungReducedLeft h k * m : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hredMulReal hd.le
      have hstrict :
          (hughesYoungCommonDivisor h k : ℝ) * (2 * X) <
            (hughesYoungCommonDivisor h k : ℝ) *
              (hughesYoungReducedLeft h k : ℝ) :=
        mul_lt_mul_of_pos_left hlarge hd
      push_cast at hsupp
      rw [hfactor] at hsupp
      have hcoord :
          (hughesYoungCommonDivisor h k : ℝ) *
              (hughesYoungReducedLeft h k : ℝ) ≤
            (hughesYoungCommonDivisor h k : ℝ) *
              (hughesYoungReducedLeft h k : ℝ) * (m : ℝ) := by
        convert hmul using 1
        all_goals push_cast
        all_goals ring
      have hupper :
          (hughesYoungCommonDivisor h k : ℝ) *
                (hughesYoungReducedLeft h k : ℝ) * (m : ℝ) ≤
            (hughesYoungCommonDivisor h k : ℝ) * (2 * X) := by
        calc
          _ ≤ 2 * ((hughesYoungCommonDivisor h k : ℝ) * X) := hsupp.2
          _ = _ := by ring
      exact (not_lt_of_ge (hcoord.trans hupper)) hstrict
    unfold hughesYoungPreReducedIntegratedBoxWeight
    dsimp only
    rw [hcut]
    simp

theorem hughesYoungLocalizedOffDiagonalBox_eq_zero_of_right_scale
    (T c H : ℝ) {X Y : ℝ} {h k M N : ℕ}
    (hY : 0 < Y) (hh : 0 < h)
    (hlarge : 2 * Y < (hughesYoungReducedRight h k : ℝ)) :
    hughesYoungLocalizedOffDiagonalBox T c H X Y h k M N = 0 := by
  unfold hughesYoungLocalizedOffDiagonalBox
    finiteQuadraticDivisorOffDiagonal
  apply Finset.sum_eq_zero
  intro m hm
  apply Finset.sum_eq_zero
  intro n hn
  by_cases hs : quadraticDivisorShift h k m n = 0
  · simp [hs]
  · simp only [hs, if_false]
    have hnPos : 0 < n := by
      have := (Finset.mem_Icc.mp hn).1
      omega
    have hd : (0 : ℝ) < hughesYoungCommonDivisor h k := by
      exact_mod_cast hughesYoungCommonDivisor_pos hh
    have hfactor : (k : ℝ) =
        (hughesYoungCommonDivisor h k : ℝ) *
          (hughesYoungReducedRight h k : ℝ) := by
      exact_mod_cast (hughesYoungCommonDivisor_mul_reducedRight h k).symm
    have hcut : hughesYoungDyadicCutoffAt
        ((hughesYoungCommonDivisor h k : ℝ) * Y)
        ((k * n : ℕ) : ℝ) = 0 := by
      by_contra hne
      have hsupp := support_hughesYoungDyadicCutoffAt_subset
        (mul_pos hd hY) hne
      have hnOne : 1 ≤ n := hnPos
      have hredMul : hughesYoungReducedRight h k ≤
          hughesYoungReducedRight h k * n := by
        simpa only [mul_one] using
          Nat.mul_le_mul_left (hughesYoungReducedRight h k) hnOne
      have hredMulReal : (hughesYoungReducedRight h k : ℝ) ≤
          ((hughesYoungReducedRight h k * n : ℕ) : ℝ) := by
        exact_mod_cast hredMul
      have hmul :
          (hughesYoungCommonDivisor h k : ℝ) *
              (hughesYoungReducedRight h k : ℝ) ≤
            (hughesYoungCommonDivisor h k : ℝ) *
              ((hughesYoungReducedRight h k * n : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hredMulReal hd.le
      have hstrict :
          (hughesYoungCommonDivisor h k : ℝ) * (2 * Y) <
            (hughesYoungCommonDivisor h k : ℝ) *
              (hughesYoungReducedRight h k : ℝ) :=
        mul_lt_mul_of_pos_left hlarge hd
      push_cast at hsupp
      rw [hfactor] at hsupp
      have hcoord :
          (hughesYoungCommonDivisor h k : ℝ) *
              (hughesYoungReducedRight h k : ℝ) ≤
            (hughesYoungCommonDivisor h k : ℝ) *
              (hughesYoungReducedRight h k : ℝ) * (n : ℝ) := by
        convert hmul using 1
        all_goals push_cast
        all_goals ring
      have hupper :
          (hughesYoungCommonDivisor h k : ℝ) *
                (hughesYoungReducedRight h k : ℝ) * (n : ℝ) ≤
            (hughesYoungCommonDivisor h k : ℝ) * (2 * Y) := by
        calc
          _ ≤ 2 * ((hughesYoungCommonDivisor h k : ℝ) * Y) := hsupp.2
          _ = _ := by ring
      exact (not_lt_of_ge (hcoord.trans hupper)) hstrict
    unfold hughesYoungPreReducedIntegratedBoxWeight
    dsimp only
    rw [hcut]
    simp

/-- Every regular canonical box can be passed to the exact large/small DFI
consumer unless it vanishes before meeting the positive arithmetic lattice. -/
theorem exists_hughesYoungCanonicalRegularBox_scale_split
    (ε : ℝ) (hε0 : 0 < ε) (hε4 : ε < 4) (q : ℕ) :
    ∃ Cγnear Cnear Lnear Cγfar Dfar Lfar Cγsmall Dsmall Lsmall : ℝ,
      0 < Cγnear ∧ 0 < Cnear ∧ 0 < Lnear ∧
      0 < Cγfar ∧ 0 < Dfar ∧ 0 < Lfar ∧
      0 < Cγsmall ∧ 0 < Dsmall ∧ 0 < Lsmall ∧
      ∃ CwFar CwSmall : ℕ → ℝ,
        (∀ r, 0 < CwFar r) ∧ (∀ r, 0 < CwSmall r) ∧
      ∀ {T P : ℝ} {h k i j : ℕ},
      Real.exp 1 ≤ T → 16 ≤ T → 0 < h → 0 < k →
      1 ≤ P → P ≤ T →
      4 * Cγfar * hughesYoungSmallContour T ≤ 1 →
      4 * Cγsmall * hughesYoungSmallContour T ≤ 1 →
      (hughesYoungLocalizedOffDiagonalBox T
          (hughesYoungSmallContour T) (T / 8)
          (hughesYoungFullDyadicScale (i + 1))
          (hughesYoungFullDyadicScale (j + 1)) h k
          (hughesYoungFullDyadicBound (i + 1))
          (hughesYoungFullDyadicBound (j + 1)) = 0) ∨
      ((64 ≤ hughesYoungDFIOptimalU P
          (hughesYoungFullDyadicScale (i + 1))
          (hughesYoungFullDyadicScale (j + 1)) ∧
        ‖hughesYoungLocalizedOffDiagonalBox T
            (hughesYoungSmallContour T) (T / 8)
            (hughesYoungFullDyadicScale (i + 1))
            (hughesYoungFullDyadicScale (j + 1)) h k
            (hughesYoungFullDyadicBound (i + 1))
            (hughesYoungFullDyadicBound (j + 1))‖ ≤
          hughesYoungLargeBoxMajorant Cγnear Cnear Lnear CwFar Dfar Lfar
            q T P (hughesYoungFullDyadicScale (i + 1))
            (hughesYoungFullDyadicScale (j + 1)) ε h k
            (hughesYoungFullDyadicBound (i + 1))
            (hughesYoungFullDyadicBound (j + 1))) ∨
       (hughesYoungDFIOptimalU P
          (hughesYoungFullDyadicScale (i + 1))
          (hughesYoungFullDyadicScale (j + 1)) < 64 ∧
        ‖hughesYoungLocalizedOffDiagonalBox T
            (hughesYoungSmallContour T) (T / 8)
            (hughesYoungFullDyadicScale (i + 1))
            (hughesYoungFullDyadicScale (j + 1)) h k
            (hughesYoungFullDyadicBound (i + 1))
            (hughesYoungFullDyadicBound (j + 1))‖ ≤
          hughesYoungSmallBoxMajorant CwSmall Dsmall Lsmall q T
            (hughesYoungFullDyadicScale (i + 1))
            (hughesYoungFullDyadicScale (j + 1)) ε h k
            (hughesYoungFullDyadicBound (i + 1))
            (hughesYoungFullDyadicBound (j + 1)))) := by
  obtain ⟨Cγnear, Cnear, Lnear, Cγfar, Dfar, Lfar,
      Cγsmall, Dsmall, Lsmall, hCγnear, hCnear, hLnear,
      hCγfar, hDfar, hLfar, hCγsmall, hDsmall, hLsmall,
      CwFar, CwSmall, hCwFar, hCwSmall, hsplit⟩ :=
    exists_hughesYoungLocalizedOffDiagonalBox_scale_split ε hε0 hε4 q
  refine ⟨Cγnear, Cnear, Lnear, Cγfar, Dfar, Lfar,
    Cγsmall, Dsmall, Lsmall, hCγnear, hCnear, hLnear,
    hCγfar, hDfar, hLfar, hCγsmall, hDsmall, hLsmall,
    CwFar, CwSmall, hCwFar, hCwSmall, ?_⟩
  intro T P h k i j hTexp hT16 hh hk hP hPT hfar hsmall
  let X := hughesYoungFullDyadicScale (i + 1)
  let Y := hughesYoungFullDyadicScale (j + 1)
  let M := hughesYoungFullDyadicBound (i + 1)
  let N := hughesYoungFullDyadicBound (j + 1)
  by_cases haX : ((hughesYoungReducedLeft h k : ℕ) : ℝ) ≤ 2 * X
  · by_cases hbY : ((hughesYoungReducedRight h k : ℕ) : ℝ) ≤ 2 * Y
    · right
      exact hsplit hTexp hT16
        (one_le_hughesYoungFullDyadicScale_succ i)
        (one_le_hughesYoungFullDyadicScale_succ j) hh hk hP hPT
        (two_mul_fullDyadicScale_div_le_bound
          (hughesYoungReducedLeft_pos hh))
        (two_mul_fullDyadicScale_div_le_bound
          (hughesYoungReducedRight_pos hh hk))
        haX hbY hfar hsmall
    · left
      exact hughesYoungLocalizedOffDiagonalBox_eq_zero_of_right_scale
        T (hughesYoungSmallContour T) (T / 8)
        (hughesYoungFullDyadicScale_pos (j + 1)) hh
        (lt_of_not_ge hbY)
  · left
    exact hughesYoungLocalizedOffDiagonalBox_eq_zero_of_left_scale
      T (hughesYoungSmallContour T) (T / 8)
      (hughesYoungFullDyadicScale_pos (i + 1)) hh
      (lt_of_not_ge haX)

end RiemannZeta.GuthMaynard
