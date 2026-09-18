import Tao2026.SmoothNumberSaddleHTSaddleComparison

/-!
# Uniform comparison of the HT main term with the smooth saddle

Finite Abel summation against Chebyshev's theta function bounds
`sum_{p <= y} (log p) p^(-sigma)` directly at the scale
`y^(1-sigma)/(1-sigma)`.  Consequently the exact saddle equation controls
the Hildebrand--Tenenbaum main coefficient with no auxiliary cutoff relating
the saddle divisor to `sqrt y`.
-/

namespace Tao2026

open scoped BigOperators Chebyshev

noncomputable section

noncomputable def saddlePrimeLogRpowSum (y : ℕ) (sigma : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 2 y).filter Nat.Prime,
    Real.log p * (p : ℝ) ^ (-sigma)

theorem saddlePrimeLogRpowSum_eq_sum_Ioc (y : ℕ) (sigma : ℝ) :
    saddlePrimeLogRpowSum y sigma =
      ∑ n ∈ Finset.Ioc 0 y, (n : ℝ) ^ (-sigma) * primeLog n := by
  have hsets :
      (Finset.Icc 2 y).filter Nat.Prime =
        (Finset.Ioc 0 y).filter Nat.Prime := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    constructor
    · intro h
      exact ⟨⟨by omega, h.1.2⟩, h.2⟩
    · exact fun h ↦ ⟨⟨h.2.two_le, h.1.2⟩, h.2⟩
  rw [saddlePrimeLogRpowSum, hsets]
  simp [primeLog, Finset.sum_filter, mul_comm]

theorem saddlePrimeLogRpowSum_abel
    {y : ℕ} (hy : 0 < y) (sigma : ℝ) :
    saddlePrimeLogRpowSum y sigma =
      (y : ℝ) ^ (-sigma) * Chebyshev.theta y +
        ∑ n ∈ Finset.Ioc 0 (y - 1),
          ((n : ℝ) ^ (-sigma) - (n + 1 : ℕ) ^ (-sigma)) *
            Chebyshev.theta n := by
  rw [saddlePrimeLogRpowSum_eq_sum_Ioc]
  have hab := Finset.sum_Ioc_by_parts
    (f := fun n : ℕ ↦ (n : ℝ) ^ (-sigma)) (g := primeLog) hy
  simp only [smul_eq_mul, sum_range_primeLog] at hab
  rw [hab]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · norm_num
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem saddlePrimeLogRpowSum_abel_Ico
    {y : ℕ} (hy : 2 ≤ y) (sigma : ℝ) :
    saddlePrimeLogRpowSum y sigma =
      (y : ℝ) ^ (-sigma) * Chebyshev.theta y +
        ∑ n ∈ Finset.Ico 2 y,
          ((n : ℝ) ^ (-sigma) - (n + 1 : ℕ) ^ (-sigma)) *
            Chebyshev.theta n := by
  rw [saddlePrimeLogRpowSum_abel (by omega) sigma]
  congr 1
  have hsets : Finset.Ioc 0 (y - 1) = Finset.Ico 1 y := by
    ext n
    simp
    omega
  have hthetaOne : Chebyshev.theta (1 : ℝ) = 0 := by
    rw [Chebyshev.theta_eq_sum_Icc]
    have hone : ⌊(1 : ℝ)⌋₊ = 1 := by norm_num
    rw [hone]
    have hfilter : (Finset.Icc 0 1).filter Nat.Prime = ∅ := by
      ext n
      constructor
      · intro hn
        have hnData := Finset.mem_filter.mp hn
        have hnTwo := hnData.2.two_le
        have hnOne := (Finset.mem_Icc.mp hnData.1).2
        have : False := by omega
        exact this.elim
      · intro hn
        simp at hn
    rw [hfilter]
    simp
  rw [hsets, ← Finset.sum_Ico_consecutive _ (by norm_num : 1 ≤ 2) hy]
  simp [hthetaOne]

theorem saddlePrimeLogRpowSum_le_mainScale
    {y : ℕ} (hy : 2 ≤ y) {sigma : ℝ}
    (hsigma : 0 ≤ sigma) (hsigmaOne : sigma < 1) :
    saddlePrimeLogRpowSum y sigma ≤
      Real.log 4 * ((y : ℝ) ^ (1 - sigma) / (1 - sigma)) := by
  have hlogFour : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  have hyPos : (0 : ℝ) < y := by positivity
  have hbeta : 0 < 1 - sigma := sub_pos.mpr hsigmaOne
  rw [saddlePrimeLogRpowSum_abel_Ico hy sigma]
  have hendpoint :
      (y : ℝ) ^ (-sigma) * Chebyshev.theta y ≤
        Real.log 4 * (y : ℝ) ^ (1 - sigma) := by
    calc
      (y : ℝ) ^ (-sigma) * Chebyshev.theta y ≤
          (y : ℝ) ^ (-sigma) * (Real.log 4 * y) := by
        exact mul_le_mul_of_nonneg_left
          (Chebyshev.theta_le_log4_mul_x (by positivity))
          (Real.rpow_nonneg hyPos.le _)
      _ = Real.log 4 * ((y : ℝ) ^ (-sigma) * y) := by ring
      _ = Real.log 4 * (y : ℝ) ^ (1 - sigma) := by
        rw [rpow_neg_mul_self hyPos]
  have hsummand (n : ℕ) (hn : n ∈ Finset.Ico 2 y) :
      ((n : ℝ) ^ (-sigma) - (n + 1 : ℕ) ^ (-sigma)) *
          Chebyshev.theta n ≤
        Real.log 4 * sigma * (n : ℝ) ^ (-sigma) := by
    have hnTwo : 2 ≤ n := (Finset.mem_Ico.mp hn).1
    have hnPos : (0 : ℝ) < n := by positivity
    have hdiffNonneg := natCast_rpow_neg_backwardDifference_nonneg
      (n := n) (by omega) hsigma
    have hdiff := natCast_rpow_neg_backwardDifference_le
      (n := n) (by omega) hsigma hsigmaOne.le
    have htheta := Chebyshev.theta_le_log4_mul_x
      (x := (n : ℝ)) (by positivity)
    calc
      ((n : ℝ) ^ (-sigma) - (n + 1 : ℕ) ^ (-sigma)) *
          Chebyshev.theta n ≤
          ((n : ℝ) ^ (-sigma) - (n + 1 : ℕ) ^ (-sigma)) *
            (Real.log 4 * n) :=
        mul_le_mul_of_nonneg_left htheta hdiffNonneg
      _ ≤ ((n : ℝ) ^ (-sigma) * (sigma / n)) *
            (Real.log 4 * n) := by
        exact mul_le_mul_of_nonneg_right hdiff
          (mul_nonneg hlogFour (by positivity))
      _ = Real.log 4 * sigma * (n : ℝ) ^ (-sigma) := by
        field_simp [ne_of_gt hnPos]
  have hsum :
      (∑ n ∈ Finset.Ico 2 y,
          ((n : ℝ) ^ (-sigma) - (n + 1 : ℕ) ^ (-sigma)) *
            Chebyshev.theta n) ≤
        Real.log 4 * sigma *
          ∑ n ∈ Finset.Ico 2 y, (n : ℝ) ^ (-sigma) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun n hn ↦ hsummand n hn
  have hpowers := sum_rpow_neg_Ico_le hy hsigma hsigmaOne
  have hcoeff : 0 ≤ Real.log 4 * sigma := mul_nonneg hlogFour hsigma
  calc
    (y : ℝ) ^ (-sigma) * Chebyshev.theta y +
        ∑ n ∈ Finset.Ico 2 y,
          ((n : ℝ) ^ (-sigma) - (n + 1 : ℕ) ^ (-sigma)) *
            Chebyshev.theta n ≤
      Real.log 4 * (y : ℝ) ^ (1 - sigma) +
        Real.log 4 * sigma *
          ∑ n ∈ Finset.Ico 2 y, (n : ℝ) ^ (-sigma) :=
      add_le_add hendpoint hsum
    _ ≤ Real.log 4 * (y : ℝ) ^ (1 - sigma) +
        Real.log 4 * sigma *
          ((y : ℝ) ^ (1 - sigma) / (1 - sigma)) := by
      gcongr
    _ = Real.log 4 * ((y : ℝ) ^ (1 - sigma) / (1 - sigma)) := by
      field_simp [ne_of_gt hbeta]
      ring

def smoothSaddleHTSharpComparisonConstant : ℝ := 5 * Real.log 4

theorem smoothSaddleHTSharpComparisonConstant_pos :
    0 < smoothSaddleHTSharpComparisonConstant := by
  unfold smoothSaddleHTSharpComparisonConstant
  positivity

theorem smoothSaddlePrimeTerm_le_five_mul_log_mul_rpow
    {p : ℕ} (hp : p.Prime) {sigma : ℝ}
    (hsigmaHalf : (1 / 2 : ℝ) ≤ sigma) (hsigmaOne : sigma ≤ 1) :
    smoothSaddlePrimeTerm p sigma ≤
      5 * Real.log p * (p : ℝ) ^ (-sigma) := by
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hbase := smoothSaddlePrimeTerm_le_five_mul_rpow_mul_log_div
    (y := p) hp le_rfl hsigmaHalf hsigmaOne
  calc
    smoothSaddlePrimeTerm p sigma ≤
        5 * (p : ℝ) ^ (1 - sigma) * (Real.log p / p) := hbase
    _ = 5 * Real.log p * (p : ℝ) ^ (-sigma) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one]
      calc
        5 * (p : ℝ) ^ (1 - sigma) *
            (Real.log p * (p : ℝ) ^ (-1 : ℝ)) =
            5 * Real.log p *
              ((p : ℝ) ^ (1 - sigma) * (p : ℝ) ^ (-1 : ℝ)) := by ring
        _ = 5 * Real.log p * (p : ℝ) ^ (-sigma) := by
          rw [← Real.rpow_add hpPos]
          congr 2
          ring

theorem smoothSaddlePhiOne_le_sharp_ht_mainScale
    {y : ℕ} (hy : 2 ≤ y) {sigma : ℝ}
    (hsigmaHalf : (1 / 2 : ℝ) ≤ sigma) (hsigmaOne : sigma < 1) :
    smoothSaddlePhiOne y sigma ≤
      smoothSaddleHTSharpComparisonConstant *
        ((y : ℝ) ^ (1 - sigma) / (1 - sigma)) := by
  have hsum := saddlePrimeLogRpowSum_le_mainScale hy
    (show 0 ≤ sigma by linarith) hsigmaOne
  have hphi : smoothSaddlePhiOne y sigma ≤
      5 * saddlePrimeLogRpowSum y sigma := by
    unfold smoothSaddlePhiOne saddlePrimeLogRpowSum
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    simpa [mul_assoc] using
      (smoothSaddlePrimeTerm_le_five_mul_log_mul_rpow
        (Finset.mem_filter.mp hp).2 hsigmaHalf hsigmaOne.le)
  calc
    smoothSaddlePhiOne y sigma ≤ 5 * saddlePrimeLogRpowSum y sigma := hphi
    _ ≤ 5 * (Real.log 4 *
        ((y : ℝ) ^ (1 - sigma) / (1 - sigma))) := by gcongr
    _ = smoothSaddleHTSharpComparisonConstant *
        ((y : ℝ) ^ (1 - sigma) / (1 - sigma)) := by
      unfold smoothSaddleHTSharpComparisonConstant
      ring

theorem smoothRankinRatio_div_sharp_htConstant_le_saddleMainCoefficient
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (hsigmaHalf : (1 / 2 : ℝ) ≤ smoothSaddlePoint X y)
    (hsigmaOne : smoothSaddlePoint X y < 1) :
    smoothRankinRatio X y / smoothSaddleHTSharpComparisonConstant ≤
      (y : ℝ) ^ (1 - smoothSaddlePoint X y) /
        ((1 - smoothSaddlePoint X y) * Real.log y) := by
  let sigma := smoothSaddlePoint X y
  let A : ℝ := (y : ℝ) ^ (1 - sigma)
  let beta : ℝ := 1 - sigma
  let L : ℝ := Real.log y
  have hbeta : 0 < beta := by dsimp [beta, sigma]; linarith
  have hC : 0 < smoothSaddleHTSharpComparisonConstant :=
    smoothSaddleHTSharpComparisonConstant_pos
  have hL : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast (lt_of_lt_of_le one_lt_two hy))
  have hphi := smoothSaddlePhiOne_le_sharp_ht_mainScale
    hy hsigmaHalf hsigmaOne
  rw [smoothSaddlePhiOne_smoothSaddlePoint hX hy] at hphi
  have huL : smoothRankinRatio X y * L ≤
      smoothSaddleHTSharpComparisonConstant * (A / beta) := by
    calc
      smoothRankinRatio X y * L = Real.log (X : ℝ) := by
        dsimp [L]
        exact smoothRankinRatio_mul_log (by omega)
      _ ≤ smoothSaddleHTSharpComparisonConstant * (A / beta) := by
        simpa only [sigma, A, beta] using hphi
  apply (div_le_iff₀ hC).2
  change smoothRankinRatio X y ≤
    (A / (beta * L)) * smoothSaddleHTSharpComparisonConstant
  have heq : A / (beta * L) * smoothSaddleHTSharpComparisonConstant =
      smoothSaddleHTSharpComparisonConstant * (A / beta) / L := by
    field_simp [ne_of_gt hbeta, ne_of_gt hL]
  rw [heq]
  exact (le_div_iff₀ hL).2 huL

theorem smoothSaddleHTMangoldtCosineMainTerm_div_log_lower_sharp
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (hsigmaHalf : (1 / 2 : ℝ) ≤ smoothSaddlePoint X y)
    (hsigmaOne : smoothSaddlePoint X y < 1) (t : ℝ) :
    smoothRankinRatio X y /
          (2 * smoothSaddleHTSharpComparisonConstant) * t ^ 2 /
        ((1 - smoothSaddlePoint X y) ^ 2 + t ^ 2) ≤
      smoothSaddleHTMangoldtCosineMainTerm y
        (1 - smoothSaddlePoint X y) t / Real.log y := by
  let sigma := smoothSaddlePoint X y
  let A : ℝ := (y : ℝ) ^ (1 - sigma)
  let beta : ℝ := 1 - sigma
  let L : ℝ := Real.log y
  let D : ℝ := beta ^ 2 + t ^ 2
  have hbeta : 0 < beta := by dsimp [beta, sigma]; linarith
  have hL : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast (lt_of_lt_of_le one_lt_two hy))
  have hD : 0 < D := by dsimp [D]; positivity
  have hC : 0 < smoothSaddleHTSharpComparisonConstant :=
    smoothSaddleHTSharpComparisonConstant_pos
  have hcomp := smoothRankinRatio_div_sharp_htConstant_le_saddleMainCoefficient
    hX hy hsigmaHalf hsigmaOne
  have hmain := smoothSaddleHTMangoldtCosineMainTerm_lower
    (y := y) (t := t) hbeta
  have hfactor : 0 ≤ t ^ 2 / (2 * D) := by positivity
  change smoothRankinRatio X y /
      (2 * smoothSaddleHTSharpComparisonConstant) * t ^ 2 / D ≤
    smoothSaddleHTMangoldtCosineMainTerm y beta t / L
  calc
    smoothRankinRatio X y /
          (2 * smoothSaddleHTSharpComparisonConstant) * t ^ 2 / D =
        (smoothRankinRatio X y / smoothSaddleHTSharpComparisonConstant) *
          (t ^ 2 / (2 * D)) := by
      field_simp [ne_of_gt hC, ne_of_gt hD]
    _ ≤ (A / (beta * L)) * (t ^ 2 / (2 * D)) :=
      mul_le_mul_of_nonneg_right (by
        simpa only [sigma, A, beta, L] using hcomp) hfactor
    _ = (A * t ^ 2 / (2 * beta * D)) / L := by
      field_simp [ne_of_gt hbeta, ne_of_gt hL, ne_of_gt hD]
    _ ≤ smoothSaddleHTMangoldtCosineMainTerm y beta t / L :=
      div_le_div_of_nonneg_right (by
        simpa only [A, D] using hmain) hL.le

end

end Tao2026
