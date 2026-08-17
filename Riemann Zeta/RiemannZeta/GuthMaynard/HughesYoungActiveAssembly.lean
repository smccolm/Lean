import RiemannZeta.GuthMaynard.HughesYoungActiveGlobal
import RiemannZeta.GuthMaynard.HughesYoungDiagonalConsumer

open Complex Finset Filter MeasureTheory Set Topology
open scoped BigOperators Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Source assembly for the active Hughes--Young family

This file identifies the finite small-contour active expression with the
literal dyadic moments consumed by the DFI estimates.  The identity retains
the actual mollifier coefficients, reduced indices, smooth cutoffs and
height integral.
-/

/-- Pointwise identification of the active small-contour truncation with
the finite sum of literal dyadic arithmetic terms. -/
theorem mollifierPair_mul_activeIntegratedSmall_eq_finiteDyadicTerms
    (T t H : ℝ) (h k R K : ℕ) :
    hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
        hughesYoungActiveIntegratedSmall T
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t H =
      ∑ ij ∈ hughesYoungActiveDyadicBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
          ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
            hughesYoungFullDyadicArithmeticTerm T t
              (hughesYoungSmallContour T) H h k ij.1 ij.2 (m, n) := by
  unfold hughesYoungActiveIntegratedSmall hughesYoungMollifierPairTerm
    hughesYoungFullDyadicArithmeticTerm hughesYoungFiniteArithmeticTerm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij _hij
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  ring

/-- After the height average, the finite active small-contour expression is
exactly the active dyadic moment. -/
theorem integral_mollifierPair_mul_activeIntegratedSmall_eq_activeDyadicMoment
    {T : ℝ} (hT : Real.exp 1 ≤ T) (H : ℝ)
    {h k R K : ℕ} (hh : 0 < h) (hk : 0 < k) :
    (∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
      (hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
        hughesYoungActiveIntegratedSmall T
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t H)) =
      hughesYoungActiveDyadicMoment T (hughesYoungSmallContour T) H h k R K := by
  classical
  let B := hughesYoungActiveDyadicBoxes
    (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hc : 0 < hughesYoungSmallContour T := (hughesYoungSmallContour_spec hT).1
  have hterm : ∀ ij ∈ B,
      ∀ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
      ∀ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
      Integrable (fun t : ℝ => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungFullDyadicArithmeticTerm T t
          (hughesYoungSmallContour T) H h k ij.1 ij.2 (m, n)) := by
    intro ij _hij m hm n hn
    unfold hughesYoungFullDyadicArithmeticTerm
    have hi := (integrable_weight_mul_hughesYoungFiniteArithmeticTerm
      (p := (m, n)) hT0 hc H hh hk
      (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hm).1)
      (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hn).1)).const_mul
        ((hughesYoungFullDyadicCutoff ij.1
          ((hughesYoungReducedLeft h k * m : ℕ) : ℝ) : ℂ) *
        (hughesYoungFullDyadicCutoff ij.2
          ((hughesYoungReducedRight h k * n : ℕ) : ℝ) : ℂ))
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hi
  have hfun : (fun t : ℝ => (hughesYoungHeightWeight T t : ℂ) *
      (hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
        hughesYoungActiveIntegratedSmall T
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t H)) =
      fun t : ℝ => ∑ ij ∈ B,
        ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
          ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
            (hughesYoungHeightWeight T t : ℂ) *
              hughesYoungFullDyadicArithmeticTerm T t
                (hughesYoungSmallContour T) H h k ij.1 ij.2 (m, n) := by
    funext t
    rw [mollifierPair_mul_activeIntegratedSmall_eq_finiteDyadicTerms]
    simp_rw [B, Finset.mul_sum]
  rw [hfun]
  unfold hughesYoungActiveDyadicMoment
  rw [MeasureTheory.integral_finsetSum B (fun ij hij =>
    integrable_finsetSum _ (fun m hm =>
      integrable_finsetSum _ (fun n hn => hterm ij hij m hm n hn)))]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [hughesYoungFullDyadicIntegratedBox_eq_finiteSum
    T (hughesYoungSmallContour T) H hh hk]
  rw [MeasureTheory.integral_finsetSum _ (fun m hm =>
    integrable_finsetSum _ (fun n hn => hterm ij hij m hm n hn))]
  apply Finset.sum_congr rfl
  intro m hm
  rw [MeasureTheory.integral_finsetSum _ (fun n hn => hterm ij hij m hm n hn)]
  apply Finset.sum_congr rfl
  intro n _hn
  rfl

/-- The finite-height active source term is integrable in the physical
height for each positive mollifier pair. -/
theorem integrable_weight_mul_mollifierPair_activeIntegratedSmall
    {T : ℝ} (hT : Real.exp 1 ≤ T) (H : ℝ)
    {h k R K : ℕ} (hh : 0 < h) (hk : 0 < k) :
    Integrable (fun t : ℝ => (hughesYoungHeightWeight T t : ℂ) *
      (hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
        hughesYoungActiveIntegratedSmall T
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t H)) := by
  classical
  let B := hughesYoungActiveDyadicBoxes
    (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hc : 0 < hughesYoungSmallContour T := (hughesYoungSmallContour_spec hT).1
  have hterm : ∀ ij ∈ B,
      ∀ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
      ∀ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
      Integrable (fun t : ℝ => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungFullDyadicArithmeticTerm T t
          (hughesYoungSmallContour T) H h k ij.1 ij.2 (m, n)) := by
    intro ij _hij m hm n hn
    unfold hughesYoungFullDyadicArithmeticTerm
    have hi := (integrable_weight_mul_hughesYoungFiniteArithmeticTerm
      (p := (m, n)) hT0 hc H hh hk
      (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hm).1)
      (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hn).1)).const_mul
        ((hughesYoungFullDyadicCutoff ij.1
          ((hughesYoungReducedLeft h k * m : ℕ) : ℝ) : ℂ) *
        (hughesYoungFullDyadicCutoff ij.2
          ((hughesYoungReducedRight h k * n : ℕ) : ℝ) : ℂ))
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hi
  have hfun : (fun t : ℝ => (hughesYoungHeightWeight T t : ℂ) *
      (hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
        hughesYoungActiveIntegratedSmall T
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t H)) =
      fun t : ℝ => ∑ ij ∈ B,
        ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
          ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
            (hughesYoungHeightWeight T t : ℂ) *
              hughesYoungFullDyadicArithmeticTerm T t
                (hughesYoungSmallContour T) H h k ij.1 ij.2 (m, n) := by
    funext t
    rw [mollifierPair_mul_activeIntegratedSmall_eq_finiteDyadicTerms]
    simp_rw [B, Finset.mul_sum]
  rw [hfun]
  exact integrable_finsetSum B (fun ij hij =>
    integrable_finsetSum _ (fun m hm =>
      integrable_finsetSum _ (fun n hn => hterm ij hij m hm n hn)))

/-- The complete finite-height active Hughes--Young integrand. -/
noncomputable def hughesYoungActiveFiniteTwistedIntegrand
    (T H : ℝ) (R K : ℕ) (t : ℝ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
        hughesYoungActiveIntegratedSmall T
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t H

/-- The complete finite-height active Hughes--Young expression, before its
diagonal/off-diagonal split. -/
noncomputable def hughesYoungActiveFiniteSmoothedMoment
    (T H : ℝ) (R K : ℕ) : ℂ :=
  ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
    hughesYoungActiveFiniteTwistedIntegrand T H R K t

/-- Exact global finite-height source assembly. -/
theorem hughesYoungActiveFiniteSmoothedMoment_eq_sum_dyadicMoments
    {T : ℝ} (hT : Real.exp 1 ≤ T) (H : ℝ) (R K : ℕ) :
    hughesYoungActiveFiniteSmoothedMoment T H R K =
      ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          hughesYoungActiveDyadicMoment T (hughesYoungSmallContour T)
            H h k R K := by
  classical
  let S := Finset.Icc 1 ((detectorCutoff T) ^ 2)
  have hpair : ∀ h ∈ S, ∀ k ∈ S,
      Integrable (fun t : ℝ => (hughesYoungHeightWeight T t : ℂ) *
        (hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
          hughesYoungActiveIntegratedSmall T
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t H)) := by
    intro h hh k hk
    exact integrable_weight_mul_mollifierPair_activeIntegratedSmall hT H
      (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hh).1)
      (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hk).1)
  unfold hughesYoungActiveFiniteSmoothedMoment
    hughesYoungActiveFiniteTwistedIntegrand
  simp_rw [Finset.mul_sum]
  rw [MeasureTheory.integral_finsetSum S (fun h hh =>
    integrable_finsetSum S (fun k hk => hpair h hh k hk))]
  apply Finset.sum_congr rfl
  intro h hh
  rw [MeasureTheory.integral_finsetSum S (fun k hk => hpair h hh k hk)]
  apply Finset.sum_congr rfl
  intro k hk
  exact integral_mollifierPair_mul_activeIntegratedSmall_eq_activeDyadicMoment
    hT H
      (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hh).1)
      (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hk).1)

/-- The literal diagonal part of the global finite active source. -/
noncomputable def hughesYoungActiveFiniteDiagonal
    (T H : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      hughesYoungActiveDyadicDiagonal T (hughesYoungSmallContour T)
        H h k R K

/-- The literal nonzero-shift part of the global finite active source. -/
noncomputable def hughesYoungActiveFiniteOffDiagonal
    (T H : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      hughesYoungActiveDyadicOffDiagonal T (hughesYoungSmallContour T)
        H h k R K

/-- Exact global diagonal/off-diagonal decomposition after the finite active
contour transfer. -/
theorem hughesYoungActiveFiniteSmoothedMoment_eq_diagonal_add_offDiagonal
    {T : ℝ} (hT : Real.exp 1 ≤ T) (H : ℝ) (R K : ℕ) :
    hughesYoungActiveFiniteSmoothedMoment T H R K =
      hughesYoungActiveFiniteDiagonal T H R K +
        hughesYoungActiveFiniteOffDiagonal T H R K := by
  rw [hughesYoungActiveFiniteSmoothedMoment_eq_sum_dyadicMoments hT]
  unfold hughesYoungActiveFiniteDiagonal hughesYoungActiveFiniteOffDiagonal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  exact hughesYoungActiveDyadicMoment_eq_diagonal_add_offDiagonal
    T (hughesYoungSmallContour T) H
      (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hh).1)
      (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hk).1)

/-- Quantitative removal of the small-contour ordinate cutoff for the exact
finite active family.  The bound retains the actual dyadic rectangles; this
is the form needed before the global source scales are chosen. -/
theorem exists_norm_hughesYoungActiveWholeSmall_sub_integrated_le :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ {T t H : ℝ} {a b R K : ℕ},
      Real.exp 1 ≤ T → t ∈ Set.Icc (T / 4) (4 * T) → 0 ≤ H →
      ‖hughesYoungActiveWholeSmall T a b R K t -
          hughesYoungActiveIntegratedSmall T a b R K t H‖ ≤
        ∑ ij ∈ hughesYoungActiveDyadicBoxes a b R K,
          ∑ _m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
            ∑ _n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
              (Real.log T * Real.exp (4 * C) * D *
                  (max (hughesYoungFullDyadicBound ij.1)
                    (hughesYoungFullDyadicBound ij.2) : ℝ) ^ 2) *
                (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40)) := by
  obtain ⟨C, D, hC, hD, hweight⟩ :=
    exists_norm_hughesYoungRightContourWeight_small_le_gaussian
  refine ⟨C, D, hC, hD, ?_⟩
  intro T t H a b R K hT ht hH
  classical
  unfold hughesYoungActiveWholeSmall hughesYoungActiveIntegratedSmall
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ ij ∈ hughesYoungActiveDyadicBoxes a b R K,
        ((∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
            ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
              (hughesYoungFullDyadicCutoff ij.1 ((a * m : ℕ) : ℝ) : ℂ) *
                (hughesYoungFullDyadicCutoff ij.2 ((b * n : ℕ) : ℝ) : ℂ) *
                ∫ u : ℝ, hughesYoungRightPairTerm t
                  (hughesYoungSmallContour T) u (m, n)) -
          (∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
            ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
              (hughesYoungFullDyadicCutoff ij.1 ((a * m : ℕ) : ℝ) : ℂ) *
                (hughesYoungFullDyadicCutoff ij.2 ((b * n : ℕ) : ℝ) : ℂ) *
                ∫ u in -H..H, hughesYoungRightPairTerm t
                  (hughesYoungSmallContour T) u (m, n)))‖ ≤
      ∑ ij ∈ hughesYoungActiveDyadicBoxes a b R K,
        ‖(∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
            ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
              (hughesYoungFullDyadicCutoff ij.1 ((a * m : ℕ) : ℝ) : ℂ) *
                (hughesYoungFullDyadicCutoff ij.2 ((b * n : ℕ) : ℝ) : ℂ) *
                ∫ u : ℝ, hughesYoungRightPairTerm t
                  (hughesYoungSmallContour T) u (m, n)) -
          (∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
            ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
              (hughesYoungFullDyadicCutoff ij.1 ((a * m : ℕ) : ℝ) : ℂ) *
                (hughesYoungFullDyadicCutoff ij.2 ((b * n : ℕ) : ℝ) : ℂ) *
                ∫ u in -H..H, hughesYoungRightPairTerm t
                  (hughesYoungSmallContour T) u (m, n))‖ := norm_sum_le _ _
    _ ≤ ∑ ij ∈ hughesYoungActiveDyadicBoxes a b R K,
        ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
          ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
            ‖(hughesYoungFullDyadicCutoff ij.1 ((a * m : ℕ) : ℝ) : ℂ) *
              (hughesYoungFullDyadicCutoff ij.2 ((b * n : ℕ) : ℝ) : ℂ) *
              ((∫ u : ℝ, hughesYoungRightPairTerm t
                    (hughesYoungSmallContour T) u (m, n)) -
                ∫ u in -H..H, hughesYoungRightPairTerm t
                  (hughesYoungSmallContour T) u (m, n))‖ := by
      apply Finset.sum_le_sum
      intro ij _hij
      rw [← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _hm => ?_)
      rw [← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _hn => ?_)
      rw [mul_sub]
    _ ≤ ∑ ij ∈ hughesYoungActiveDyadicBoxes a b R K,
        ∑ _m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
          ∑ _n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
            (Real.log T * Real.exp (4 * C) * D *
                (max (hughesYoungFullDyadicBound ij.1)
                  (hughesYoungFullDyadicBound ij.2) : ℝ) ^ 2) *
              (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40)) := by
      apply Finset.sum_le_sum
      intro ij _hij
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro n hn
      let M := max (hughesYoungFullDyadicBound ij.1)
        (hughesYoungFullDyadicBound ij.2)
      have hM : 0 < M := (hughesYoungFullDyadicBound_pos ij.1).trans_le
        (Nat.le_max_left _ _)
      have hm0 : 0 < m := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hm).1
      have hn0 : 0 < n := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hn).1
      have hpair := norm_hughesYoungWholePairTerm_sub_interval_le
        (M := M) (p := (m, n)) hD hweight hT ht hH hM hm0 hn0
        ((Finset.mem_Icc.mp hm).2.trans (Nat.le_max_left _ _))
        ((Finset.mem_Icc.mp hn).2.trans (Nat.le_max_right _ _))
      have hcutI : ‖(hughesYoungFullDyadicCutoff ij.1
          ((a * m : ℕ) : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact abs_hughesYoungDyadicCutoffAt_le_one
          (hughesYoungFullDyadicScale_pos ij.1) (by positivity)
      have hcutJ : ‖(hughesYoungFullDyadicCutoff ij.2
          ((b * n : ℕ) : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact abs_hughesYoungDyadicCutoffAt_le_one
          (hughesYoungFullDyadicScale_pos ij.2) (by positivity)
      rw [norm_mul, norm_mul]
      calc
        ‖(hughesYoungFullDyadicCutoff ij.1 ((a * m : ℕ) : ℝ) : ℂ)‖ *
            ‖(hughesYoungFullDyadicCutoff ij.2 ((b * n : ℕ) : ℝ) : ℂ)‖ *
            ‖(∫ u : ℝ, hughesYoungRightPairTerm t
                  (hughesYoungSmallContour T) u (m, n)) -
              ∫ u in -H..H, hughesYoungRightPairTerm t
                (hughesYoungSmallContour T) u (m, n)‖ ≤
          1 * 1 * ‖(∫ u : ℝ, hughesYoungRightPairTerm t
                  (hughesYoungSmallContour T) u (m, n)) -
              ∫ u in -H..H, hughesYoungRightPairTerm t
                (hughesYoungSmallContour T) u (m, n)‖ := by gcongr
        _ ≤ (Real.log T * Real.exp (4 * C) * D * (M : ℝ) ^ 2) *
              (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40)) := by
          simpa only [one_mul] using hpair
        _ = _ := by simp only [M, Nat.cast_max]

/-- The exact finite majorant used for one active vertical-tail family. -/
noncomputable def hughesYoungActiveVerticalTailPairMajorant
    (C D T H : ℝ) (a b R K : ℕ) : ℝ :=
  ∑ ij ∈ hughesYoungActiveDyadicBoxes a b R K,
    ∑ _m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
      ∑ _n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
        (Real.log T * Real.exp (4 * C) * D *
            (max (hughesYoungFullDyadicBound ij.1)
              (hughesYoungFullDyadicBound ij.2) : ℝ) ^ 2) *
          (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40))

theorem hughesYoungActiveVerticalTailPairMajorant_nonneg
    {T H C D : ℝ} (hT : Real.exp 1 ≤ T) (hD : 0 ≤ D)
    (a b R K : ℕ) :
    0 ≤ hughesYoungActiveVerticalTailPairMajorant C D T H a b R K := by
  have hT1 : (1 : ℝ) ≤ T := by linarith [Real.exp_one_gt_d9]
  unfold hughesYoungActiveVerticalTailPairMajorant
  apply Finset.sum_nonneg
  intro ij _hij
  apply Finset.sum_nonneg
  intro m _hm
  apply Finset.sum_nonneg
  intro n _hn
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (Real.log_nonneg hT1) (Real.exp_pos _).le) hD)
        (sq_nonneg _))
    (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _))

/-- The exact finite mollifier-weighted vertical-tail majorant. -/
noncomputable def hughesYoungActiveVerticalTailMajorant
    (C D T H : ℝ) (R K : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖ *
        (1 / Real.pi) *
        hughesYoungActiveVerticalTailPairMajorant C D T H
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K

theorem hughesYoungActiveVerticalTailMajorant_nonneg
    {T H C D : ℝ} (hT : Real.exp 1 ≤ T) (hD : 0 ≤ D)
    (R K : ℕ) :
    0 ≤ hughesYoungActiveVerticalTailMajorant C D T H R K := by
  unfold hughesYoungActiveVerticalTailMajorant
  apply Finset.sum_nonneg
  intro h _hh
  apply Finset.sum_nonneg
  intro k _hk
  exact mul_nonneg (mul_nonneg
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity))
    (hughesYoungActiveVerticalTailPairMajorant_nonneg hT hD _ _ R K)

/-- Uniform pointwise comparison between the whole and finite-height active
source integrands. -/
theorem exists_norm_hughesYoungActiveWholeTwistedIntegrand_sub_finite_le :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ {T t H : ℝ} {R K : ℕ},
      Real.exp 1 ≤ T → t ∈ Set.Icc (T / 4) (4 * T) → 0 ≤ H →
      ‖hughesYoungActiveWholeTwistedIntegrand T R K t -
          hughesYoungActiveFiniteTwistedIntegrand T H R K t‖ ≤
        hughesYoungActiveVerticalTailMajorant C D T H R K := by
  obtain ⟨C, D, hC, hD, hpair⟩ :=
    exists_norm_hughesYoungActiveWholeSmall_sub_integrated_le
  refine ⟨C, D, hC, hD, ?_⟩
  intro T t H R K hT ht hH
  classical
  unfold hughesYoungActiveWholeTwistedIntegrand
    hughesYoungActiveFiniteTwistedIntegrand
    hughesYoungActiveVerticalTailMajorant
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ((∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
            hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
              hughesYoungActiveWholeSmall T
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t) -
          ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
            hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
              hughesYoungActiveIntegratedSmall T
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t H)‖ ≤
      ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ‖∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
            hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
              hughesYoungActiveWholeSmall T
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t -
          ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
            hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
              hughesYoungActiveIntegratedSmall T
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t H‖ :=
      norm_sum_le _ _
    _ ≤ ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          ‖hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
            (hughesYoungActiveWholeSmall T
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t -
              hughesYoungActiveIntegratedSmall T
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t H)‖ := by
      apply Finset.sum_le_sum
      intro h _hh
      rw [← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _hk => ?_)
      rw [mul_sub]
    _ ≤ ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          ‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖ *
            (1 / Real.pi) *
            hughesYoungActiveVerticalTailPairMajorant C D T H
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K := by
      apply Finset.sum_le_sum
      intro h hh
      apply Finset.sum_le_sum
      intro k hk
      have hh0 : 0 < h := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hh).1
      have hk0 : 0 < k := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hk).1
      have hmoll := norm_hughesYoungMollifierPairTerm_le T t hh0 hk0
      have htail := hpair hT ht hH (a := hughesYoungReducedLeft h k)
        (b := hughesYoungReducedRight h k) (R := R) (K := K)
      have htail' :
          ‖hughesYoungActiveWholeSmall T
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t -
              hughesYoungActiveIntegratedSmall T
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t H‖ ≤
            hughesYoungActiveVerticalTailPairMajorant C D T H
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K := by
        simpa only [hughesYoungActiveVerticalTailPairMajorant] using htail
      have hpi : ‖(1 / (Real.pi : ℂ))‖ = 1 / Real.pi := by
        simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      rw [norm_mul, norm_mul, hpi]
      calc
        ‖hughesYoungMollifierPairTerm T t h k‖ * (1 / Real.pi) *
            ‖hughesYoungActiveWholeSmall T
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t -
              hughesYoungActiveIntegratedSmall T
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t H‖ ≤
          (‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖) *
            (1 / Real.pi) *
            hughesYoungActiveVerticalTailPairMajorant C D T H
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K := by
          gcongr
        _ = _ := by ring

/-- Integrability of the global finite-height active expression. -/
theorem integrable_weight_mul_hughesYoungActiveFiniteTwistedIntegrand
    {T : ℝ} (hT : Real.exp 1 ≤ T) (H : ℝ) (R K : ℕ) :
    Integrable (fun t : ℝ => (hughesYoungHeightWeight T t : ℂ) *
      hughesYoungActiveFiniteTwistedIntegrand T H R K t) := by
  classical
  let S := Finset.Icc 1 ((detectorCutoff T) ^ 2)
  unfold hughesYoungActiveFiniteTwistedIntegrand
  simp_rw [Finset.mul_sum]
  exact integrable_finsetSum S (fun h hh =>
    integrable_finsetSum S (fun k hk =>
      integrable_weight_mul_mollifierPair_activeIntegratedSmall hT H
        (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hh).1)
        (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hk).1)))

/-- Quantitative global comparison between the whole active source and its
finite-height DFI realization. -/
theorem exists_norm_hughesYoungActiveWholeSmoothedMoment_sub_finite_le :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ {q R K : ℕ}, 0 < q → 0 < R →
      ∀ {η : ℝ}, 0 < η → η < 2 * (q : ℝ) - 1 / 2 →
      ∀ {T H : ℝ}, Real.exp 1 ≤ T → 0 ≤ H →
      (∀ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∀ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          (((hughesYoungReducedLeft h k) *
            (hughesYoungReducedRight h k) * R : ℕ) : ℝ) ≤
              hughesYoungDyadicRatio ^ (K + 1)) →
      ‖hughesYoungActiveWholeSmoothedMoment T R K -
          hughesYoungActiveFiniteSmoothedMoment T H R K‖ ≤
        (15 * T / 4) * hughesYoungActiveVerticalTailMajorant C D T H R K := by
  obtain ⟨C, D, hC, hD, hpoint⟩ :=
    exists_norm_hughesYoungActiveWholeTwistedIntegrand_sub_finite_le
  refine ⟨C, D, hC, hD, ?_⟩
  intro q R K hq hR η hη0 hη T H hT hH hcover
  have hwhole := integrable_weight_mul_hughesYoungActiveWholeTwistedIntegrand
    hq hR η hη0 hη hT hcover
  have hfinite :=
    integrable_weight_mul_hughesYoungActiveFiniteTwistedIntegrand hT H R K
  let A := hughesYoungActiveVerticalTailMajorant C D T H R K
  let B : ℝ → ℝ := Set.Icc (T / 4) (4 * T) |>.indicator (fun _ => A)
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hA0 : 0 ≤ A :=
    hughesYoungActiveVerticalTailMajorant_nonneg hT hD.le R K
  have hBint : Integrable B := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const isCompact_Icc.measure_ne_top
  unfold hughesYoungActiveWholeSmoothedMoment
    hughesYoungActiveFiniteSmoothedMoment
  rw [← integral_sub hwhole hfinite]
  apply (norm_integral_le_of_norm_le hBint ?_).trans_eq
  · rw [show (∫ t : ℝ, B t) = ∫ _t in Set.Icc (T / 4) (4 * T), A by
        exact MeasureTheory.integral_indicator measurableSet_Icc]
    rw [MeasureTheory.setIntegral_const]
    simp only [smul_eq_mul, measureReal_def, Real.volume_Icc]
    rw [ENNReal.toReal_ofReal (by nlinarith : 0 ≤ 4 * T - T / 4)]
    unfold A
    ring
  · filter_upwards with t
    by_cases hw : hughesYoungHeightWeight T t = 0
    · have hleft :
          ‖(hughesYoungHeightWeight T t : ℂ) *
                hughesYoungActiveWholeTwistedIntegrand T R K t -
              (hughesYoungHeightWeight T t : ℂ) *
                hughesYoungActiveFiniteTwistedIntegrand T H R K t‖ = 0 := by
          simp [hw]
      rw [hleft]
      simpa only [B] using
        (Set.indicator_nonneg (s := Set.Icc (T / 4) (4 * T))
          (fun _ _ => hA0) t)
    · have ht : t ∈ Set.Icc (T / 4) (4 * T) :=
        hughesYoungHeightWeight_support hT0 hw
      have hdiff := hpoint hT ht hH (R := R) (K := K)
      have hw0 := hughesYoungHeightWeight_nonneg T t
      have hw1 := hughesYoungHeightWeight_le_one T t
      rw [show
          (hughesYoungHeightWeight T t : ℂ) *
                hughesYoungActiveWholeTwistedIntegrand T R K t -
              (hughesYoungHeightWeight T t : ℂ) *
                hughesYoungActiveFiniteTwistedIntegrand T H R K t =
            (hughesYoungHeightWeight T t : ℂ) *
              (hughesYoungActiveWholeTwistedIntegrand T R K t -
                hughesYoungActiveFiniteTwistedIntegrand T H R K t) by ring,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
      change _ ≤ Set.indicator (Set.Icc (T / 4) (4 * T)) (fun _ => A) t
      rw [Set.indicator_of_mem ht]
      exact (mul_le_mul_of_nonneg_left hdiff hw0).trans
        (by simpa only [A, one_mul] using
          mul_le_mul_of_nonneg_right hw1 hA0)

end RiemannZeta.GuthMaynard
