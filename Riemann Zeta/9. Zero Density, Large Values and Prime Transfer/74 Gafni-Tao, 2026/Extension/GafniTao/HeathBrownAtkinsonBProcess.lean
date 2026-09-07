import GafniTao.HeathBrownAtkinsonCurvatureScale
import RiemannZeta.GuthMaynard.SecondOrderMeanValue

/-!
# The B-process for a difference of Atkinson phases

This file passes the exact equation-(11) phase difference to the frozen
second-derivative van der Corput theorem.  The lower and upper curvature
parameters are explicit functions of the physical height gap and index box.
-/

open Set
open RiemannZeta.GuthMaynard

namespace GafniTao

noncomputable section

/-- Orient the two-height phase difference so that its second derivative is
positive when `u < t`. -/
def heathBrownAtkinsonPositiveDifference (t u x : ℝ) : ℝ :=
  heathBrownAtkinsonRealPhase u x - heathBrownAtkinsonRealPhase t x

theorem hasDerivAt_heathBrownAtkinsonPositiveDifference
    {t u x : ℝ} (ht : 0 < t) (hu : 0 < u) (hx : 0 < x) :
    HasDerivAt (heathBrownAtkinsonPositiveDifference t u)
      (heathBrownAtkinsonRealSlope u x -
        heathBrownAtkinsonRealSlope t x) x := by
  unfold heathBrownAtkinsonPositiveDifference heathBrownAtkinsonRealSlope
  exact (hasDerivAt_heathBrownAtkinsonRealPhase hu hx).sub
    (hasDerivAt_heathBrownAtkinsonRealPhase ht hx)

theorem hasDerivAt_heathBrownAtkinsonPositiveDifferenceSlope
    {t u x : ℝ} (ht : 0 < t) (hu : 0 < u) (hx : 0 < x) :
    HasDerivAt
      (fun y => heathBrownAtkinsonRealSlope u y -
        heathBrownAtkinsonRealSlope t y)
      (heathBrownAtkinsonRealCurvature u x -
        heathBrownAtkinsonRealCurvature t x) x :=
  (hasDerivAt_heathBrownAtkinsonRealSlope hu hx).sub
    (hasDerivAt_heathBrownAtkinsonRealSlope ht hx)

/-- Exact second-order mean-value identity for the positively oriented phase
difference. -/
theorem exists_heathBrownAtkinsonPositiveDifference_secondDifference
    {t u x : ℝ} (ht : 0 < t) (hu : 0 < u) (hx : 0 < x) :
    ∃ xi ∈ Set.Ioo x (x + 2),
      heathBrownAtkinsonRealCurvature u xi -
          heathBrownAtkinsonRealCurvature t xi =
        (heathBrownAtkinsonPositiveDifference t u (x + 2) -
          heathBrownAtkinsonPositiveDifference t u (x + 1)) -
        (heathBrownAtkinsonPositiveDifference t u (x + 1) -
          heathBrownAtkinsonPositiveDifference t u x) := by
  let F : ℝ → ℝ := heathBrownAtkinsonPositiveDifference t u
  let F' : ℝ → ℝ := fun y =>
    heathBrownAtkinsonRealSlope u y - heathBrownAtkinsonRealSlope t y
  let F'' : ℝ → ℝ := fun y =>
    heathBrownAtkinsonRealCurvature u y -
      heathBrownAtkinsonRealCurvature t y
  have hmv := second_order_mean_value F F' F'' x
    (fun y hy => by
      dsimp only [F, F']
      exact hasDerivAt_heathBrownAtkinsonPositiveDifference ht hu
        (hx.trans_le hy.1))
    (fun y hy => by
      dsimp only [F', F'']
      exact hasDerivAt_heathBrownAtkinsonPositiveDifferenceSlope ht hu
        (hx.trans_le hy.1))
  obtain ⟨xi, hxi, heq⟩ := hmv
  refine ⟨xi, hxi, ?_⟩
  dsimp only [F, F''] at heq ⊢
  calc
    _ = F (x + 2) - 2 * F (x + 1) + F x := heq
    _ = (F (x + 2) - F (x + 1)) -
        (F (x + 1) - F x) := by ring

/-- The natural-index phase used by the finite B-process. -/
def heathBrownAtkinsonPositiveDifferenceNat
    (t u : ℝ) (K n : ℕ) : ℝ :=
  heathBrownAtkinsonPhase u (K + n) -
    heathBrownAtkinsonPhase t (K + n)

/-- The real and natural versions of the positively oriented phase agree at
natural indices. -/
theorem heathBrownAtkinsonPositiveDifference_natCast
    (t u : ℝ) (K n : ℕ) :
    heathBrownAtkinsonPositiveDifference t u (K + n : ℕ) =
      heathBrownAtkinsonPositiveDifferenceNat t u K n := by
  unfold heathBrownAtkinsonPositiveDifference
    heathBrownAtkinsonPositiveDifferenceNat
  rw [heathBrownAtkinsonRealPhase_natCast,
    heathBrownAtkinsonRealPhase_natCast]

/-- Explicit lower curvature parameter for a block `K <= K+n <= K+N+2`. -/
def heathBrownAtkinsonBProcessLambda
    (t u : ℝ) (K N : ℕ) : ℝ :=
  heathBrownAtkinsonBoxCurvatureLower u K (K + N + 2) * (t - u)

/-- Explicit upper curvature parameter for the same block. -/
def heathBrownAtkinsonBProcessLambdaUpper
    (t u : ℝ) (K N : ℕ) : ℝ :=
  heathBrownAtkinsonBoxCurvatureUpper u K (K + N + 2) * (t - u)

theorem heathBrownAtkinsonBProcessLambda_pos
    {t u : ℝ} {K N : ℕ} (hu : 0 < u) (htu : u < t) (hK : 0 < K) :
    0 < heathBrownAtkinsonBProcessLambda t u K N := by
  unfold heathBrownAtkinsonBProcessLambda
    heathBrownAtkinsonBoxCurvatureLower
  have hB : 0 < (K + N + 2 : ℕ) := by omega
  exact mul_pos
    (div_pos Real.pi_pos
      (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos (by exact_mod_cast hB)))
        (heathBrownAtkinsonSlopeUpper_pos hu (by exact_mod_cast hK))))
    (sub_pos.mpr htu)

/-- Every unit-spaced second difference of the exact natural phase is
bounded by the explicit dyadic curvature parameters. -/
theorem heathBrownAtkinsonPositiveDifferenceNat_secondDifference_bounds
    {t u : ℝ} {K N : ℕ}
    (hu : 0 < u) (htu : u < t) (hK : 0 < K)
    (hblock : ((K + N + 2 : ℕ) : ℝ) ≤ u)
    (htUpper : t ≤ 2 * u) :
    ∀ n, n < N →
      heathBrownAtkinsonBProcessLambda t u K N ≤
          (heathBrownAtkinsonPositiveDifferenceNat t u K (n + 2) -
            heathBrownAtkinsonPositiveDifferenceNat t u K (n + 1)) -
          (heathBrownAtkinsonPositiveDifferenceNat t u K (n + 1) -
            heathBrownAtkinsonPositiveDifferenceNat t u K n) ∧
        (heathBrownAtkinsonPositiveDifferenceNat t u K (n + 2) -
            heathBrownAtkinsonPositiveDifferenceNat t u K (n + 1)) -
          (heathBrownAtkinsonPositiveDifferenceNat t u K (n + 1) -
            heathBrownAtkinsonPositiveDifferenceNat t u K n) ≤
        heathBrownAtkinsonBProcessLambdaUpper t u K N := by
  intro n hn
  have ht : 0 < t := hu.trans htu
  have hx : 0 < ((K + n : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < K + n by omega)
  obtain ⟨xi, hxi, heq⟩ :=
    exists_heathBrownAtkinsonPositiveDifference_secondDifference ht hu hx
  have hAxi : (K : ℝ) ≤ xi := by
    have : (K : ℝ) ≤ ((K + n : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right K n
    exact this.trans hxi.1.le
  have hxiB : xi ≤ ((K + N + 2 : ℕ) : ℝ) := by
    have hncast : ((K + n : ℕ) : ℝ) + 2 ≤
        ((K + N + 2 : ℕ) : ℝ) := by
      exact_mod_cast (show K + n + 2 ≤ K + N + 2 by omega)
    exact hxi.2.le.trans hncast
  have hbox := heathBrownAtkinsonCurvatureDerivative_box_bounds hu
    (by exact_mod_cast hK) hAxi hxiB
  have hpoint := heathBrownAtkinsonCurvatureDifference_bounds hu htu
    (hx.trans hxi.1) (hxiB.trans hblock) htUpper
  have hgap : 0 ≤ t - u := sub_nonneg.mpr htu.le
  have hlower := (mul_le_mul_of_nonneg_right hbox.1 hgap).trans hpoint.1
  have hupper := hpoint.2.trans (mul_le_mul_of_nonneg_right hbox.2 hgap)
  have heqNat :
      heathBrownAtkinsonRealCurvature u xi -
          heathBrownAtkinsonRealCurvature t xi =
        (heathBrownAtkinsonPositiveDifferenceNat t u K (n + 2) -
          heathBrownAtkinsonPositiveDifferenceNat t u K (n + 1)) -
        (heathBrownAtkinsonPositiveDifferenceNat t u K (n + 1) -
          heathBrownAtkinsonPositiveDifferenceNat t u K n) := by
    have htwo : ((K + n : ℕ) : ℝ) + 2 = ((K + (n + 2) : ℕ) : ℝ) := by
      push_cast
      ring
    have hone : ((K + n : ℕ) : ℝ) + 1 = ((K + (n + 1) : ℕ) : ℝ) := by
      push_cast
      ring
    calc
      _ = (heathBrownAtkinsonPositiveDifference t u
              (((K + (n + 2) : ℕ) : ℝ)) -
            heathBrownAtkinsonPositiveDifference t u
              (((K + (n + 1) : ℕ) : ℝ))) -
          (heathBrownAtkinsonPositiveDifference t u
              (((K + (n + 1) : ℕ) : ℝ)) -
            heathBrownAtkinsonPositiveDifference t u
              (((K + n : ℕ) : ℝ))) := by
          rw [heq, htwo, hone]
      _ = _ := by
        simp only [heathBrownAtkinsonPositiveDifference_natCast]
  unfold heathBrownAtkinsonBProcessLambda
    heathBrownAtkinsonBProcessLambdaUpper
  rw [show -(heathBrownAtkinsonRealCurvature t xi -
      heathBrownAtkinsonRealCurvature u xi) =
      heathBrownAtkinsonRealCurvature u xi -
        heathBrownAtkinsonRealCurvature t xi by ring] at hlower hupper
  rw [heqNat] at hlower hupper
  push_cast at hlower hupper ⊢
  have hpair := And.intro hlower hupper
  simpa only [add_assoc] using hpair

/-- The frozen van der Corput B-process applied to the exact two-height
Atkinson phase. -/
theorem heathBrownAtkinsonPositiveDifference_B_process
    {t u : ℝ} {K N : ℕ}
    (hu : 0 < u) (htu : u < t) (hK : 0 < K)
    (hblock : ((K + N + 2 : ℕ) : ℝ) ≤ u)
    (htUpper : t ≤ 2 * u) :
    ‖∑ n ∈ Finset.range (N + 1),
        unitaryPhase (heathBrownAtkinsonPositiveDifferenceNat t u K n)‖ ≤
      ((N : ℝ) * heathBrownAtkinsonBProcessLambdaUpper t u K N /
          (2 * Real.pi) + 2) *
        (2 * Real.pi /
            Real.sqrt (heathBrownAtkinsonBProcessLambda t u K N) +
          2 * (Real.sqrt (heathBrownAtkinsonBProcessLambda t u K N) /
            heathBrownAtkinsonBProcessLambda t u K N + 1)) := by
  apply vanDerCorput_B_process
  · exact heathBrownAtkinsonBProcessLambda_pos hu htu hK
  · intro n hn
    exact (heathBrownAtkinsonPositiveDifferenceNat_secondDifference_bounds
      hu htu hK hblock htUpper n hn).1
  · intro n hn
    exact (heathBrownAtkinsonPositiveDifferenceNat_secondDifference_bounds
      hu htu hK hblock htUpper n hn).2


end

end GafniTao
