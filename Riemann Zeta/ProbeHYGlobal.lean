import RiemannZeta.GuthMaynard.HughesYoungGlobalBounds

open Complex Finset Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff FourierTransform Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

theorem probe_integrated_term_le
    {T c H : ℝ} {h k i j m n : ℕ}
    (hh : 0 < h) (hk : 0 < k) :
    ‖hughesYoungFullDyadicIntegratedTerm T c H h k i j (m, n)‖ ≤
      ‖∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungFiniteArithmeticTerm T t c H h k (m, n)‖ := by
  rw [hughesYoungFullDyadicIntegratedTerm_eq_source T c H hh hk,
    integral_hughesYoungFiniteArithmeticTerm_eq_source T c H hh hk]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (hughesYoungFullDyadicCutoff_nonneg_nat _ _),
    abs_of_nonneg (hughesYoungFullDyadicCutoff_nonneg_nat _ _)]
  have hleft := (hughesYoungDyadicCutoffAt_mem_Icc
    (hughesYoungFullDyadicScale_pos i) (by positivity : (0 : ℝ) ≤
      ((hughesYoungReducedLeft h k * m : ℕ) : ℝ))).2
  have hright := (hughesYoungDyadicCutoffAt_mem_Icc
    (hughesYoungFullDyadicScale_pos j) (by positivity : (0 : ℝ) ≤
      ((hughesYoungReducedRight h k * n : ℕ) : ℝ))).2
  have hleft' : hughesYoungFullDyadicCutoff i
      ((hughesYoungReducedLeft h k * m : ℕ) : ℝ) ≤ 1 := by
    simpa only [hughesYoungFullDyadicCutoff] using hleft
  have hright' : hughesYoungFullDyadicCutoff j
      ((hughesYoungReducedRight h k * n : ℕ) : ℝ) ≤ 1 := by
    simpa only [hughesYoungFullDyadicCutoff] using hright
  have hprod : hughesYoungFullDyadicCutoff i
          ((hughesYoungReducedLeft h k * m : ℕ) : ℝ) *
        hughesYoungFullDyadicCutoff j
          ((hughesYoungReducedRight h k * n : ℕ) : ℝ) ≤ 1 := by
    calc
      _ ≤ 1 * 1 := mul_le_mul hleft' hright'
        (hughesYoungFullDyadicCutoff_nonneg_nat _ _) (by norm_num)
      _ = 1 := one_mul 1
  calc
    hughesYoungFullDyadicCutoff i
          ((hughesYoungReducedLeft h k * m : ℕ) : ℝ) *
        hughesYoungFullDyadicCutoff j
          ((hughesYoungReducedRight h k * n : ℕ) : ℝ) *
        ‖divisorWeight m‖ * ‖divisorWeight n‖ *
          ‖hughesYoungIntegratedSourceWeight T c H h k
            ((h * m : ℕ) : ℝ) ((k * n : ℕ) : ℝ)‖ ≤
      1 * ‖divisorWeight m‖ * ‖divisorWeight n‖ *
          ‖hughesYoungIntegratedSourceWeight T c H h k
            ((h * m : ℕ) : ℝ) ((k * n : ℕ) : ℝ)‖ := by
              gcongr
    _ = _ := by ring

noncomputable def probeActiveCutoff (T : ℝ) (R : ℕ) : ℕ :=
  4 * ((detectorCutoff T) ^ 2 * (detectorCutoff T) ^ 2 * R) + 1

theorem probe_active_diagonal_bound :
    ∃ C W : ℝ, 0 < C ∧ 0 < W ∧
      ∀ {T H : ℝ} {R K : ℕ}, Real.exp 1 ≤ T → 0 ≤ H →
      ‖hughesYoungActiveFiniteDiagonal T H R K‖ ≤
        ((K + 2 : ℕ) : ℝ) ^ 2 *
          ((15 * T / 4) * (1 / Real.pi) *
            (Real.log T * Real.exp (4 * C) * W *
              Real.sqrt (Real.pi / 80))) *
          hughesYoungFiniteDiagonalArithmeticMajorant T
            ((detectorCutoff T) ^ 2) (probeActiveCutoff T R) := by
  obtain ⟨C, W, hC, hW, hterm⟩ :=
    exists_norm_integral_hughesYoungFiniteArithmeticTerm_diagonal_le
  refine ⟨C, W, hC, hW, ?_⟩
  intro T H R K hT hH
  let ell : ℕ := (detectorCutoff T) ^ 2
  let B : ℕ := 4 * (ell * ell * R) + 1
  let F : ℝ := (15 * T / 4) * (1 / Real.pi) *
    (Real.log T * Real.exp (4 * C) * W * Real.sqrt (Real.pi / 80))
  have hF0 : 0 ≤ F := by
    have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
    have hlog : 0 ≤ Real.log T := Real.log_nonneg hT1
    dsimp only [F]
    positivity
  have hbox : ∀ h ∈ Finset.Icc 1 ell, ∀ k ∈ Finset.Icc 1 ell,
      ∀ ij ∈ hughesYoungActiveDyadicBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
      ‖hughesYoungFullDyadicDiagonalBox T (hughesYoungSmallContour T)
          H h k ij.1 ij.2‖ ≤
        F * (∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Icc 1 B,
          if h * m = k * n then
            ‖shortMobiusSquareCoeff T h‖ *
              ‖shortMobiusSquareCoeff T k‖ *
              (m.divisors.card : ℝ) * (n.divisors.card : ℝ) *
              (((h * m : ℕ) : ℝ))⁻¹
          else 0) := by
    intro h hhmem k hkmem ij hij
    have hh : 0 < h := (Finset.mem_Icc.mp hhmem).1
    have hk : 0 < k := (Finset.mem_Icc.mp hkmem).1
    have ha : hughesYoungReducedLeft h k ≤ h := hughesYoungReducedLeft_le h k
    have hb : hughesYoungReducedRight h k ≤ k := hughesYoungReducedRight_le h k
    have hab : hughesYoungReducedLeft h k * hughesYoungReducedRight h k * R ≤
        ell * ell * R := by
      gcongr
      · exact ha.trans (Finset.mem_Icc.mp hhmem).2
      · exact hb.trans (Finset.mem_Icc.mp hkmem).2
    have hBi : hughesYoungFullDyadicBound ij.1 ≤ B := by
      exact (hughesYoungFullDyadicBound_le_four_mul_activeConductor_add_one_left
        hij).trans (by dsimp only [B]; omega)
    have hBj : hughesYoungFullDyadicBound ij.2 ≤ B := by
      exact (hughesYoungFullDyadicBound_le_four_mul_activeConductor_add_one_right
        hij).trans (by dsimp only [B]; omega)
    unfold hughesYoungFullDyadicDiagonalBox
    calc
      ‖∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
          ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
            if quadraticDivisorShift h k m n = 0 then
              hughesYoungFullDyadicIntegratedTerm T
                (hughesYoungSmallContour T) H h k ij.1 ij.2 (m, n)
            else 0‖ ≤
        ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
          ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
            ‖if quadraticDivisorShift h k m n = 0 then
              hughesYoungFullDyadicIntegratedTerm T
                (hughesYoungSmallContour T) H h k ij.1 ij.2 (m, n)
            else 0‖ := (norm_sum_le _ _).trans
              (Finset.sum_le_sum fun m _ => norm_sum_le _ _)
      _ ≤ ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
          ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
            F * (if h * m = k * n then
              ‖shortMobiusSquareCoeff T h‖ *
                ‖shortMobiusSquareCoeff T k‖ *
                (m.divisors.card : ℝ) * (n.divisors.card : ℝ) *
                (((h * m : ℕ) : ℝ))⁻¹
            else 0) := by
        apply Finset.sum_le_sum
        intro m hm
        apply Finset.sum_le_sum
        intro n hn
        have hm0 : 0 < m := (Finset.mem_Icc.mp hm).1
        have hn0 : 0 < n := (Finset.mem_Icc.mp hn).1
        by_cases hd : h * m = k * n
        · have hs : quadraticDivisorShift h k m n = 0 :=
            (quadraticDivisorShift_eq_zero_iff h k m n).2 hd
          rw [if_pos hs, if_pos hd]
          exact (norm_hughesYoungFullDyadicIntegratedTerm_le hh hk).trans
            ((hterm hT hH hh hk hm0 hn0 hd).trans_eq (by dsimp only [F]; ring))
        · have hs : quadraticDivisorShift h k m n ≠ 0 := fun hs =>
            hd ((quadraticDivisorShift_eq_zero_iff h k m n).1 hs)
          simp [hd, hs]
      _ = F * (∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
          ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
            if h * m = k * n then
              ‖shortMobiusSquareCoeff T h‖ *
                ‖shortMobiusSquareCoeff T k‖ *
                (m.divisors.card : ℝ) * (n.divisors.card : ℝ) *
                (((h * m : ℕ) : ℝ))⁻¹
            else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        rw [Finset.mul_sum]
      _ ≤ F * (∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Icc 1 B,
          if h * m = k * n then
            ‖shortMobiusSquareCoeff T h‖ *
              ‖shortMobiusSquareCoeff T k‖ *
              (m.divisors.card : ℝ) * (n.divisors.card : ℝ) *
              (((h * m : ℕ) : ℝ))⁻¹
          else 0) := by
        apply mul_le_mul_of_nonneg_left _ hF0
        calc
          (∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
              ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
                if h * m = k * n then
                  ‖shortMobiusSquareCoeff T h‖ *
                    ‖shortMobiusSquareCoeff T k‖ *
                    (m.divisors.card : ℝ) * (n.divisors.card : ℝ) *
                    (((h * m : ℕ) : ℝ))⁻¹ else 0) ≤
            ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
              ∑ n ∈ Finset.Icc 1 B,
                if h * m = k * n then
                  ‖shortMobiusSquareCoeff T h‖ *
                    ‖shortMobiusSquareCoeff T k‖ *
                    (m.divisors.card : ℝ) * (n.divisors.card : ℝ) *
                    (((h * m : ℕ) : ℝ))⁻¹ else 0 := by
              apply Finset.sum_le_sum
              intro m _hm
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · exact Finset.Icc_subset_Icc_right hBj
              · intro n _hn _hnnot
                positivity
          _ ≤ ∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Icc 1 B,
                if h * m = k * n then
                  ‖shortMobiusSquareCoeff T h‖ *
                    ‖shortMobiusSquareCoeff T k‖ *
                    (m.divisors.card : ℝ) * (n.divisors.card : ℝ) *
                    (((h * m : ℕ) : ℝ))⁻¹ else 0 := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · exact Finset.Icc_subset_Icc_right hBi
              · intro m _hm _hmnot
                positivity
  unfold hughesYoungActiveFiniteDiagonal hughesYoungActiveDyadicDiagonal
  let A : ℕ → ℕ → ℝ := fun h k =>
    ∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Icc 1 B,
      if h * m = k * n then
        ‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖ *
          (m.divisors.card : ℝ) * (n.divisors.card : ℝ) *
          (((h * m : ℕ) : ℝ))⁻¹ else 0
  have hA0 : ∀ h k, 0 ≤ A h k := by
    intro h k
    dsimp only [A]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  calc
    ‖∑ h ∈ Finset.Icc 1 ell, ∑ k ∈ Finset.Icc 1 ell,
        ∑ ij ∈ hughesYoungActiveDyadicBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
          hughesYoungFullDyadicDiagonalBox T (hughesYoungSmallContour T)
            H h k ij.1 ij.2‖ ≤
      ∑ h ∈ Finset.Icc 1 ell, ∑ k ∈ Finset.Icc 1 ell,
        ∑ ij ∈ hughesYoungActiveDyadicBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
          ‖hughesYoungFullDyadicDiagonalBox T (hughesYoungSmallContour T)
            H h k ij.1 ij.2‖ := (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun h _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun k _ => norm_sum_le _ _))
    _ ≤ ∑ h ∈ Finset.Icc 1 ell, ∑ k ∈ Finset.Icc 1 ell,
        ∑ _ij ∈ hughesYoungActiveDyadicBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
          F * A h k := by
      apply Finset.sum_le_sum
      intro h hh
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro ij hij
      simpa only [A] using hbox h hh k hk ij hij
    _ ≤ ∑ h ∈ Finset.Icc 1 ell, ∑ k ∈ Finset.Icc 1 ell,
        (((K + 2 : ℕ) : ℝ) ^ 2) * (F * A h k) := by
      apply Finset.sum_le_sum
      intro h hh
      apply Finset.sum_le_sum
      intro k hk
      rw [Finset.sum_const, nsmul_eq_mul]
      push_cast
      have hcardNat := card_hughesYoungActiveDyadicBoxes_le
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K
      have hcard : ((hughesYoungActiveDyadicBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K).card : ℝ) ≤
          (((K + 2) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hcardNat
      norm_num at hcard
      exact mul_le_mul_of_nonneg_right hcard
        (mul_nonneg hF0 (hA0 h k))
    _ = (((K + 2 : ℕ) : ℝ) ^ 2) * F *
        hughesYoungFiniteDiagonalArithmeticMajorant T ell B := by
      unfold hughesYoungFiniteDiagonalArithmeticMajorant
      dsimp only [A]
      simp_rw [Finset.mul_sum]
      ring
    _ = _ := by simp only [ell, B, probeActiveCutoff]; ring

end RiemannZeta.GuthMaynard

#check eventually_log_pow_le_rpow
#check rpow_mul_log_sq_le_epsilon
