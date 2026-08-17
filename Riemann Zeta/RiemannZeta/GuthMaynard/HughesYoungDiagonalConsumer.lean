import RiemannZeta.GuthMaynard.HughesYoungFiniteComparison
import RiemannZeta.GuthMaynard.HughesYoungGlobalAssembly
import RiemannZeta.GuthMaynard.SmoothZetaAFE

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# The source diagonal in the finite Hughes--Young rectangle

The lemmas in this file start from the literal four-index arithmetic term
used by `hughesYoungFiniteRectIntegratedMoment`.  They retain the Mellin
weight and the squared Möbius coefficients until after taking norms.  This is
the missing entry bridge to the elementary `hm = kn` diagonal estimate.
-/

theorem norm_natCast_cpow_neg_afeCriticalPoint
    {n : ℕ} (hn : 0 < n) (t : ℝ) :
    ‖(n : ℂ) ^ (-afeCriticalPoint t)‖ =
      (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rw [← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hn)]
  simp [afeCriticalPoint]

/-- A single literal finite AFE term, before the height average, is bounded
by the exact divisor powers on the small contour. -/
theorem norm_hughesYoungFiniteArithmeticTerm_le
    {T t c H B : ℝ} {h k m n : ℕ}
    (hh : 0 < h) (hk : 0 < k) (hm : 0 < m) (hn : 0 < n)
    (hH : 0 ≤ H)
    (hweight :
      (∫ u in -H..H, ‖hughesYoungRightContourWeight t c u‖) ≤ B) :
    ‖hughesYoungFiniteArithmeticTerm T t c H h k (m, n)‖ ≤
      ‖shortMobiusSquareCoeff T h‖ * (h : ℝ) ^ (-(1 / 2 : ℝ)) *
      ‖shortMobiusSquareCoeff T k‖ * (k : ℝ) ^ (-(1 / 2 : ℝ)) *
      (1 / Real.pi) * B *
      ((m.divisors.card : ℝ) * (m : ℝ) ^ (-(1 / 2 + c : ℝ))) *
      ((n.divisors.card : ℝ) * (n : ℝ) ^ (-(1 / 2 + c : ℝ))) := by
  have hHH : -H ≤ H := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hscalar : ‖(1 / (Real.pi : ℂ))‖ = 1 / Real.pi := by
    simp [Real.norm_eq_abs, abs_of_pos hpi]
  have hpairPoint : ∀ u : ℝ,
      ‖hughesYoungRightPairTerm t c u (m, n)‖ =
        ‖hughesYoungRightContourWeight t c u‖ *
          ((m.divisors.card : ℝ) *
            (m : ℝ) ^ (-(1 / 2 + c : ℝ))) *
          ((n.divisors.card : ℝ) *
            (n : ℝ) ^ (-(1 / 2 + c : ℝ))) := by
    intro u
    rw [hughesYoungRightPairTerm, norm_mul, norm_mul,
      norm_divisorDirichletTerm_afe_vertical_eq t c u hm,
      norm_divisorDirichletTerm_afe_vertical_eq (-t) c u hn]
  have hpairInt :
      ‖∫ u in -H..H, hughesYoungRightPairTerm t c u (m, n)‖ ≤
        B *
          ((m.divisors.card : ℝ) *
            (m : ℝ) ^ (-(1 / 2 + c : ℝ))) *
          ((n.divisors.card : ℝ) *
            (n : ℝ) ^ (-(1 / 2 + c : ℝ))) := by
    calc
      ‖∫ u in -H..H, hughesYoungRightPairTerm t c u (m, n)‖ ≤
          ∫ u in -H..H, ‖hughesYoungRightPairTerm t c u (m, n)‖ :=
        intervalIntegral.norm_integral_le_integral_norm hHH
      _ = (∫ u in -H..H, ‖hughesYoungRightContourWeight t c u‖) *
          ((m.divisors.card : ℝ) *
            (m : ℝ) ^ (-(1 / 2 + c : ℝ))) *
          ((n.divisors.card : ℝ) *
            (n : ℝ) ^ (-(1 / 2 + c : ℝ))) := by
        simp_rw [hpairPoint]
        rw [intervalIntegral.integral_mul_const,
          intervalIntegral.integral_mul_const]
      _ ≤ B *
          ((m.divisors.card : ℝ) *
            (m : ℝ) ^ (-(1 / 2 + c : ℝ))) *
          ((n.divisors.card : ℝ) *
            (n : ℝ) ^ (-(1 / 2 + c : ℝ))) := by
        gcongr
  rw [show hughesYoungFiniteArithmeticTerm T t c H h k (m, n) =
      (shortMobiusSquareCoeff T h * (h : ℂ) ^ (-afeCriticalPoint t) *
        shortMobiusSquareCoeff T k * (k : ℂ) ^ (-afeCriticalPoint (-t)) *
        (1 / (Real.pi : ℂ))) *
          (∫ u in -H..H, hughesYoungRightPairTerm t c u (m, n)) by
    unfold hughesYoungFiniteArithmeticTerm
    ring]
  rw [norm_mul]
  calc
    ‖shortMobiusSquareCoeff T h * (h : ℂ) ^ (-afeCriticalPoint t) *
          shortMobiusSquareCoeff T k * (k : ℂ) ^ (-afeCriticalPoint (-t)) *
          (1 / (Real.pi : ℂ))‖ *
        ‖∫ u in -H..H, hughesYoungRightPairTerm t c u (m, n)‖ ≤
      ‖shortMobiusSquareCoeff T h * (h : ℂ) ^ (-afeCriticalPoint t) *
          shortMobiusSquareCoeff T k * (k : ℂ) ^ (-afeCriticalPoint (-t)) *
          (1 / (Real.pi : ℂ))‖ *
        (B *
          ((m.divisors.card : ℝ) * (m : ℝ) ^ (-(1 / 2 + c : ℝ))) *
          ((n.divisors.card : ℝ) * (n : ℝ) ^ (-(1 / 2 + c : ℝ)))) :=
      mul_le_mul_of_nonneg_left hpairInt (norm_nonneg _)
    _ = _ := by
      simp only [norm_mul, hscalar,
        norm_natCast_cpow_neg_afeCriticalPoint hh t,
        norm_natCast_cpow_neg_afeCriticalPoint hk (-t)]
      ring

/-- On `hm = kn`, the four exact critical-line powers contribute `q⁻¹`;
the positive small-contour displacement supplies two additional factors at
most one. -/
theorem hughesYoung_diagonal_rpow_product_le
    {c : ℝ} (hc : 0 ≤ c) {h k m n : ℕ}
    (hh : 0 < h) (hk : 0 < k) (hm : 0 < m) (hn : 0 < n)
    (hdiag : h * m = k * n) :
    (h : ℝ) ^ (-(1 / 2 : ℝ)) *
        (k : ℝ) ^ (-(1 / 2 : ℝ)) *
        (m : ℝ) ^ (-(1 / 2 + c : ℝ)) *
        (n : ℝ) ^ (-(1 / 2 + c : ℝ)) ≤
      (((h * m : ℕ) : ℝ))⁻¹ := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmC : (m : ℝ) ^ (-c) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hmOne (neg_nonpos.mpr hc)
  have hnC : (n : ℝ) ^ (-c) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hnOne (neg_nonpos.mpr hc)
  have hnC0 : 0 ≤ (n : ℝ) ^ (-c) :=
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hmnC : (m : ℝ) ^ (-c) * (n : ℝ) ^ (-c) ≤ 1 :=
    mul_le_one₀ hmC hnC0 hnC
  have hsplitM :
      (m : ℝ) ^ (-(1 / 2 + c : ℝ)) =
        (m : ℝ) ^ (-(1 / 2 : ℝ)) * (m : ℝ) ^ (-c) := by
    rw [← Real.rpow_add hmR]
    congr 1
    ring
  have hsplitN :
      (n : ℝ) ^ (-(1 / 2 + c : ℝ)) =
        (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-c) := by
    rw [← Real.rpow_add hnR]
    congr 1
    ring
  have hhm :
      (h : ℝ) ^ (-(1 / 2 : ℝ)) *
          (m : ℝ) ^ (-(1 / 2 : ℝ)) =
        ((h * m : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Nat.cast_mul, Real.mul_rpow (le_of_lt hhR) (le_of_lt hmR)]
  have hkn :
      (k : ℝ) ^ (-(1 / 2 : ℝ)) *
          (n : ℝ) ^ (-(1 / 2 : ℝ)) =
        ((k * n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Nat.cast_mul, Real.mul_rpow (le_of_lt hkR) (le_of_lt hnR)]
  have hqpos : (0 : ℝ) < ((h * m : ℕ) : ℝ) := by positivity
  have hqpow :
      ((h * m : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
          ((h * m : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) =
        (((h * m : ℕ) : ℝ))⁻¹ := by
    calc
      ((h * m : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
            ((h * m : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) =
          ((h * m : ℕ) : ℝ) ^ (-1 : ℝ) := by
        rw [← Real.rpow_add hqpos]
        congr 1
        ring
      _ = _ := Real.rpow_neg_one _
  rw [hsplitM, hsplitN]
  calc
    (h : ℝ) ^ (-(1 / 2 : ℝ)) *
          (k : ℝ) ^ (-(1 / 2 : ℝ)) *
          ((m : ℝ) ^ (-(1 / 2 : ℝ)) * (m : ℝ) ^ (-c)) *
          ((n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-c)) =
        (((h * m : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
          ((k * n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) *
          ((m : ℝ) ^ (-c) * (n : ℝ) ^ (-c)) := by
      rw [← hhm, ← hkn]
      ring
    _ ≤ ((((h * m : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
          ((k * n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) * 1) := by
      exact mul_le_mul_of_nonneg_left hmnC (by positivity)
    _ = (((h * m : ℕ) : ℝ))⁻¹ := by
      rw [← hdiag, mul_one, hqpow]

/-- The literal height-integrated diagonal term has the expected harmonic
factor `(hm)⁻¹`, uniformly for the finite Mellin interval `[-H,H]`. -/
theorem exists_norm_integral_hughesYoungFiniteArithmeticTerm_diagonal_le :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ {T H : ℝ} {h k m n : ℕ},
        Real.exp 1 ≤ T → 0 ≤ H →
        0 < h → 0 < k → 0 < m → 0 < n → h * m = k * n →
        ‖∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
            hughesYoungFiniteArithmeticTerm T t
              (hughesYoungSmallContour T) H h k (m, n)‖ ≤
          (15 * T / 4) *
            (‖shortMobiusSquareCoeff T h‖ *
              ‖shortMobiusSquareCoeff T k‖ * (1 / Real.pi) *
              (Real.log T * Real.exp (4 * C) * K *
                Real.sqrt (Real.pi / 80)) *
              (m.divisors.card : ℝ) * (n.divisors.card : ℝ) *
              (((h * m : ℕ) : ℝ))⁻¹) := by
  obtain ⟨C, K, hC, hK, hweight⟩ :=
    exists_uniform_intervalIntegral_norm_hughesYoungRightContourWeight_small_le
  refine ⟨C, K, hC, hK, ?_⟩
  intro T H h k m n hT hH hh hk hm hn hdiag
  let W : ℝ :=
    Real.log T * Real.exp (4 * C) * K * Real.sqrt (Real.pi / 80)
  let A : ℝ :=
    ‖shortMobiusSquareCoeff T h‖ *
      ‖shortMobiusSquareCoeff T k‖ * (1 / Real.pi) * W *
      (m.divisors.card : ℝ) * (n.divisors.card : ℝ) *
      (((h * m : ℕ) : ℝ))⁻¹
  let B : ℝ → ℝ :=
    Set.Icc (T / 4) (4 * T) |>.indicator (fun _ => A)
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hc0 : 0 ≤ hughesYoungSmallContour T :=
    (hughesYoungSmallContour_spec hT).1.le
  have hW0 : 0 ≤ W := by
    unfold W
    have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (Real.log_nonneg hT1) (Real.exp_pos _).le) hK.le)
      (Real.sqrt_nonneg _)
  have hA0 : 0 ≤ A := by
    unfold A
    positivity
  have hBint : Integrable B := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const isCompact_Icc.measure_ne_top
  apply (norm_integral_le_of_norm_le hBint ?_).trans_eq
  · rw [show (∫ t : ℝ, B t) =
        ∫ _t in Set.Icc (T / 4) (4 * T), A by
          exact MeasureTheory.integral_indicator measurableSet_Icc]
    rw [MeasureTheory.setIntegral_const]
    simp only [smul_eq_mul, measureReal_def, Real.volume_Icc]
    rw [ENNReal.toReal_ofReal (by nlinarith : 0 ≤ 4 * T - T / 4)]
    unfold A W
    ring
  · filter_upwards with t
    by_cases hw : hughesYoungHeightWeight T t = 0
    · rw [hw]
      simp only [ofReal_zero, zero_mul, norm_zero]
      simpa only [B] using Set.indicator_nonneg (fun _ _ => hA0) t
    · have ht : t ∈ Set.Icc (T / 4) (4 * T) :=
        hughesYoungHeightWeight_support hT0 hw
      have hfinite := norm_hughesYoungFiniteArithmeticTerm_le
        (T := T) (t := t) (c := hughesYoungSmallContour T) (H := H)
        hh hk hm hn hH (hweight hT ht hH)
      have hpowers := hughesYoung_diagonal_rpow_product_le
        hc0 hh hk hm hn hdiag
      have hw0 := hughesYoungHeightWeight_nonneg T t
      have hw1 := hughesYoungHeightWeight_le_one T t
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
      change _ ≤ Set.indicator (Set.Icc (T / 4) (4 * T)) (fun _ => A) t
      rw [Set.indicator_of_mem ht]
      calc
        hughesYoungHeightWeight T t *
            ‖hughesYoungFiniteArithmeticTerm T t
              (hughesYoungSmallContour T) H h k (m, n)‖ ≤
          1 *
            (‖shortMobiusSquareCoeff T h‖ *
              (h : ℝ) ^ (-(1 / 2 : ℝ)) *
              ‖shortMobiusSquareCoeff T k‖ *
              (k : ℝ) ^ (-(1 / 2 : ℝ)) *
              (1 / Real.pi) * W *
              ((m.divisors.card : ℝ) *
                (m : ℝ) ^ (-(1 / 2 + hughesYoungSmallContour T : ℝ))) *
              ((n.divisors.card : ℝ) *
                (n : ℝ) ^ (-(1 / 2 + hughesYoungSmallContour T : ℝ)))) := by
          gcongr
        _ = (‖shortMobiusSquareCoeff T h‖ *
              ‖shortMobiusSquareCoeff T k‖ * (1 / Real.pi) * W *
              (m.divisors.card : ℝ) * (n.divisors.card : ℝ)) *
            ((h : ℝ) ^ (-(1 / 2 : ℝ)) *
              (k : ℝ) ^ (-(1 / 2 : ℝ)) *
              (m : ℝ) ^ (-(1 / 2 + hughesYoungSmallContour T : ℝ)) *
              (n : ℝ) ^ (-(1 / 2 + hughesYoungSmallContour T : ℝ))) := by
          ring
        _ ≤ (‖shortMobiusSquareCoeff T h‖ *
              ‖shortMobiusSquareCoeff T k‖ * (1 / Real.pi) * W *
              (m.divisors.card : ℝ) * (n.divisors.card : ℝ)) *
            (((h * m : ℕ) : ℝ))⁻¹ := by
          exact mul_le_mul_of_nonneg_left hpowers (by positivity)
        _ = A := by
          unfold A
          ring

noncomputable def hughesYoungFiniteDiagonalArithmeticMajorant
    (T : ℝ) (ell M : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 ell, ∑ k ∈ Finset.Icc 1 ell,
    ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
      if h * m = k * n then
        ‖shortMobiusSquareCoeff T h‖ *
          ‖shortMobiusSquareCoeff T k‖ *
          (m.divisors.card : ℝ) * (n.divisors.card : ℝ) *
          (((h * m : ℕ) : ℝ))⁻¹
      else 0

noncomputable def hughesYoungRestrictedDiagonalFiber
    (T : ℝ) (ell M q : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 ell).product (Finset.Icc 1 M) with
      p.1 * p.2 = q,
    ‖shortMobiusSquareCoeff T p.1‖ * (p.2.divisors.card : ℝ)

/-- Exact finite fiber decomposition of the positive `hm = kn` majorant. -/
theorem hughesYoungFiniteDiagonalArithmeticMajorant_eq_fibers
    (T : ℝ) (ell M : ℕ) :
    hughesYoungFiniteDiagonalArithmeticMajorant T ell M =
      ∑ q ∈ Finset.Icc 1 (ell * M),
        hughesYoungRestrictedDiagonalFiber T ell M q ^ 2 *
          (q : ℝ)⁻¹ := by
  classical
  let P := (Finset.Icc 1 ell).product (Finset.Icc 1 M)
  let Q := Finset.Icc 1 (ell * M)
  let f : ℕ × ℕ → ℕ := fun p => p.1 * p.2
  let a : ℕ × ℕ → ℝ := fun p =>
    ‖shortMobiusSquareCoeff T p.1‖ * (p.2.divisors.card : ℝ)
  have hmaps : ∀ p ∈ P, f p ∈ Q := by
    intro p hp
    have hp' := Finset.mem_product.mp hp
    have hp1 := Finset.mem_Icc.mp hp'.1
    have hp2 := Finset.mem_Icc.mp hp'.2
    exact Finset.mem_Icc.mpr
      ⟨Nat.mul_pos hp1.1 hp2.1, Nat.mul_le_mul hp1.2 hp2.2⟩
  have hfiber (q : ℕ) :
      (∑ p ∈ P with f p = q, a p) =
        hughesYoungRestrictedDiagonalFiber T ell M q := by
    rfl
  have hreorder :
      (∑ h ∈ Finset.Icc 1 ell, ∑ k ∈ Finset.Icc 1 ell,
        ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
          if h * m = k * n then
            ‖shortMobiusSquareCoeff T h‖ *
              ‖shortMobiusSquareCoeff T k‖ *
              (m.divisors.card : ℝ) * (n.divisors.card : ℝ) *
              (((h * m : ℕ) : ℝ))⁻¹
          else 0) =
        ∑ h ∈ Finset.Icc 1 ell, ∑ m ∈ Finset.Icc 1 M,
          ∑ k ∈ Finset.Icc 1 ell, ∑ n ∈ Finset.Icc 1 M,
            if h * m = k * n then
              ‖shortMobiusSquareCoeff T h‖ *
                ‖shortMobiusSquareCoeff T k‖ *
                (m.divisors.card : ℝ) * (n.divisors.card : ℝ) *
                (((h * m : ℕ) : ℝ))⁻¹
            else 0 := by
    apply Finset.sum_congr rfl
    intro h _hh
    rw [Finset.sum_comm]
  have hproduct :
      (∑ p ∈ P, ∑ r ∈ P,
          if f p = f r then a p * a r * ((f p : ℕ) : ℝ)⁻¹ else 0) =
        ∑ h ∈ Finset.Icc 1 ell, ∑ m ∈ Finset.Icc 1 M,
        ∑ k ∈ Finset.Icc 1 ell, ∑ n ∈ Finset.Icc 1 M,
          if h * m = k * n then
            ‖shortMobiusSquareCoeff T h‖ *
              ‖shortMobiusSquareCoeff T k‖ *
              (m.divisors.card : ℝ) * (n.divisors.card : ℝ) *
              (((h * m : ℕ) : ℝ))⁻¹
          else 0 := by
    let F : (ℕ × ℕ) → (ℕ × ℕ) → ℝ := fun p r =>
      if f p = f r then a p * a r * ((f p : ℕ) : ℝ)⁻¹ else 0
    calc
      (∑ p ∈ P, ∑ r ∈ P, F p r) =
          ∑ p ∈ P, ∑ k ∈ Finset.Icc 1 ell, ∑ n ∈ Finset.Icc 1 M,
            F p (k, n) := by
              apply Finset.sum_congr rfl
              intro p _hp
              dsimp only [P]
              exact Finset.sum_product (β := ℝ)
                (Finset.Icc 1 ell) (Finset.Icc 1 M) (F p)
      _ = ∑ h ∈ Finset.Icc 1 ell, ∑ m ∈ Finset.Icc 1 M,
            ∑ k ∈ Finset.Icc 1 ell, ∑ n ∈ Finset.Icc 1 M,
              F (h, m) (k, n) := by
                dsimp only [P]
                exact Finset.sum_product (β := ℝ)
                  (Finset.Icc 1 ell) (Finset.Icc 1 M)
                  (fun p => ∑ k ∈ Finset.Icc 1 ell, ∑ n ∈ Finset.Icc 1 M,
                    F p (k, n))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro h _hh
        apply Finset.sum_congr rfl
        intro m _hm
        apply Finset.sum_congr rfl
        intro k _hk
        apply Finset.sum_congr rfl
        intro n _hn
        dsimp only [F, f, a]
        split_ifs <;> ring
  unfold hughesYoungFiniteDiagonalArithmeticMajorant
  rw [hreorder]
  rw [← hproduct]
  change (∑ p ∈ P, ∑ r ∈ P,
      if f p = f r then a p * a r * ((f p : ℕ) : ℝ)⁻¹ else 0) = _
  calc
    (∑ p ∈ P, ∑ r ∈ P,
        if f p = f r then a p * a r * ((f p : ℕ) : ℝ)⁻¹ else 0) =
      ∑ q ∈ Q, ∑ p ∈ P with f p = q,
        ∑ r ∈ P,
          if f p = f r then a p * a r * ((f p : ℕ) : ℝ)⁻¹ else 0 := by
      symm
      exact Finset.sum_fiberwise_of_maps_to hmaps _
    _ = ∑ q ∈ Q,
        (∑ p ∈ P with f p = q, a p) ^ 2 * (q : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro q _hq
      have hinner : ∀ p ∈ P.filter (fun p => f p = q),
          (∑ r ∈ P,
            if f p = f r then a p * a r * ((f p : ℕ) : ℝ)⁻¹ else 0) =
            a p * (∑ r ∈ P with f r = q, a r) * (q : ℝ)⁻¹ := by
        intro p hp
        have hfp : f p = q := (Finset.mem_filter.mp hp).2
        calc
          (∑ r ∈ P,
              if f p = f r then a p * a r * ((f p : ℕ) : ℝ)⁻¹ else 0) =
            ∑ r ∈ P with f r = q,
              a p * a r * ((f p : ℕ) : ℝ)⁻¹ := by
                rw [Finset.sum_filter]
                apply Finset.sum_congr rfl
                intro r _hr
                by_cases hfr : f r = q
                · simp [hfp, hfr]
                · have hqfr : q ≠ f r := fun h => hfr h.symm
                  simp [hfp, hfr, hqfr]
          _ = a p * (∑ r ∈ P with f r = q, a r) * (q : ℝ)⁻¹ := by
            rw [hfp]
            calc
              (∑ r ∈ P with f r = q, a p * a r * (q : ℝ)⁻¹) =
                  (∑ r ∈ P with f r = q, a p * a r) * (q : ℝ)⁻¹ := by
                    rw [Finset.sum_mul]
              _ = a p * (∑ r ∈ P with f r = q, a r) * (q : ℝ)⁻¹ := by
                    rw [Finset.mul_sum]
      rw [Finset.sum_congr rfl hinner]
      rw [pow_two]
      symm
      calc
        ((∑ p ∈ P with f p = q, a p) *
            (∑ r ∈ P with f r = q, a r)) * (q : ℝ)⁻¹ =
            (∑ p ∈ P with f p = q,
              a p * (∑ r ∈ P with f r = q, a r)) * (q : ℝ)⁻¹ := by
                rw [Finset.sum_mul]
        _ = ∑ p ∈ P with f p = q,
              a p * (∑ r ∈ P with f r = q, a r) * (q : ℝ)⁻¹ := by
                rw [Finset.sum_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _hq
      rw [hfiber]

/-- The finite rectangle's diagonal fiber is exactly the full divisor fiber
with the additional AFE cutoff `q / h ≤ M`. -/
theorem hughesYoungRestrictedDiagonalFiber_eq_divisor_filter
    (T : ℝ) (ell M : ℕ) {q : ℕ} (hq : 0 < q) :
    hughesYoungRestrictedDiagonalFiber T ell M q =
      ∑ h ∈ q.divisors.filter (fun h => h ≤ ell ∧ q / h ≤ M),
        ‖shortMobiusSquareCoeff T h‖ * ((q / h).divisors.card : ℝ) := by
  classical
  let P := (Finset.Icc 1 ell).product (Finset.Icc 1 M)
  let S := P.filter (fun p => p.1 * p.2 = q)
  let D := q.divisors.filter (fun h => h ≤ ell ∧ q / h ≤ M)
  unfold hughesYoungRestrictedDiagonalFiber
  change (∑ p ∈ S,
      ‖shortMobiusSquareCoeff T p.1‖ * (p.2.divisors.card : ℝ)) =
    ∑ h ∈ D,
      ‖shortMobiusSquareCoeff T h‖ * ((q / h).divisors.card : ℝ)
  apply Finset.sum_bij (fun p _hp => p.1)
  · intro p hp
    have hpS := Finset.mem_filter.mp hp
    have hpP := Finset.mem_product.mp hpS.1
    have hpH := Finset.mem_Icc.mp hpP.1
    have hpM := Finset.mem_Icc.mp hpP.2
    have hprod : p.1 * p.2 = q := hpS.2
    have hdvd : p.1 ∣ q := ⟨p.2, hprod.symm⟩
    have hquot : q / p.1 = p.2 := by
      exact (Nat.div_eq_iff_eq_mul_left hpH.1 hdvd).2 (by simpa [Nat.mul_comm] using hprod.symm)
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨hdvd, Nat.ne_of_gt hq⟩, hpH.2, by simpa [hquot] using hpM.2⟩
  · intro p hp r hr hpr
    have hpS := Finset.mem_filter.mp hp
    have hrS := Finset.mem_filter.mp hr
    have hpP := Finset.mem_product.mp hpS.1
    have hpPos := (Finset.mem_Icc.mp hpP.1).1
    apply Prod.ext
    · exact hpr
    · exact Nat.mul_left_cancel hpPos <| by
        calc
          p.1 * p.2 = q := hpS.2
          _ = r.1 * r.2 := hrS.2.symm
          _ = p.1 * r.2 := by rw [hpr]
  · intro h hh
    have hhD := Finset.mem_filter.mp hh
    have hdiv := Nat.mem_divisors.mp hhD.1
    have hhPos : 0 < h := Nat.pos_of_dvd_of_pos hdiv.1 hq
    have hquotPos : 0 < q / h := Nat.div_pos (Nat.le_of_dvd hq hdiv.1) hhPos
    refine ⟨(h, q / h), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨hhPos, hhD.2.1⟩,
          Finset.mem_Icc.mpr ⟨hquotPos, hhD.2.2⟩⟩
    · exact Nat.mul_div_cancel' hdiv.1
  · intro p hp
    have hpS := Finset.mem_filter.mp hp
    have hpP := Finset.mem_product.mp hpS.1
    have hpH := Finset.mem_Icc.mp hpP.1
    have hprod : p.1 * p.2 = q := hpS.2
    have hdvd : p.1 ∣ q := ⟨p.2, hprod.symm⟩
    have hquot : q / p.1 = p.2 := by
      exact (Nat.div_eq_iff_eq_mul_left hpH.1 hdvd).2 (by simpa [Nat.mul_comm] using hprod.symm)
    rw [hquot]

/-- The finite AFE cutoff only removes nonnegative terms from the complete
Hughes--Young divisor fiber. -/
theorem hughesYoungRestrictedDiagonalFiber_le_smoothTwistedDiagonalFiber
    (T : ℝ) (ell M : ℕ) {q : ℕ} (hq : 0 < q) :
    hughesYoungRestrictedDiagonalFiber T ell M q ≤
      smoothTwistedDiagonalFiber ell q (shortMobiusSquareCoeff T) := by
  rw [hughesYoungRestrictedDiagonalFiber_eq_divisor_filter T ell M hq]
  unfold smoothTwistedDiagonalFiber
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro h hh
    have hh' := Finset.mem_filter.mp hh
    exact Finset.mem_filter.mpr ⟨hh'.1, hh'.2.1⟩
  · intro h _hh _hnot
    positivity

/-- The complete literal finite-rectangle arithmetic majorant is controlled
by the established smooth diagonal majorant at cutoff `ell * M`. -/
theorem hughesYoungFiniteDiagonalArithmeticMajorant_le
    (T : ℝ) (ell M : ℕ) :
    hughesYoungFiniteDiagonalArithmeticMajorant T ell M ≤
      ∑ q ∈ Finset.Icc 1 (ell * M),
        smoothTwistedDiagonalFiber ell q (shortMobiusSquareCoeff T) ^ 2 *
          (q : ℝ)⁻¹ := by
  rw [hughesYoungFiniteDiagonalArithmeticMajorant_eq_fibers]
  apply Finset.sum_le_sum
  intro q hq
  have hqPos : 0 < q := (Finset.mem_Icc.mp hq).1
  have hle := hughesYoungRestrictedDiagonalFiber_le_smoothTwistedDiagonalFiber
    T ell M hqPos
  have hleft : 0 ≤ hughesYoungRestrictedDiagonalFiber T ell M q := by
    unfold hughesYoungRestrictedDiagonalFiber
    positivity
  have hright : 0 ≤ smoothTwistedDiagonalFiber ell q (shortMobiusSquareCoeff T) := by
    unfold smoothTwistedDiagonalFiber
    positivity
  have hsquare : hughesYoungRestrictedDiagonalFiber T ell M q ^ 2 ≤
      smoothTwistedDiagonalFiber ell q (shortMobiusSquareCoeff T) ^ 2 :=
    (sq_le_sq₀ hleft hright).2 hle
  exact mul_le_mul_of_nonneg_right hsquare (inv_nonneg.mpr (Nat.cast_nonneg q))

/-- The literal diagonal part of the finite Hughes--Young rectangle is
bounded by the exact positive arithmetic majorant above. -/
theorem exists_norm_hughesYoungFiniteDiagonalSum_le :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ {T H : ℝ} {M : ℕ}, Real.exp 1 ≤ T → 0 ≤ H →
        ‖∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
            ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
              hughesYoungFiniteDiagonalBox T (hughesYoungSmallContour T)
                H h k M M‖ ≤
          ((15 * T / 4) * (1 / Real.pi) *
            (Real.log T * Real.exp (4 * C) * K *
              Real.sqrt (Real.pi / 80))) *
            hughesYoungFiniteDiagonalArithmeticMajorant T
              ((detectorCutoff T) ^ 2) M := by
  obtain ⟨C, K, hC, hK, hterm⟩ :=
    exists_norm_integral_hughesYoungFiniteArithmeticTerm_diagonal_le
  refine ⟨C, K, hC, hK, ?_⟩
  intro T H M hT hH
  let ell := (detectorCutoff T) ^ 2
  let F : ℝ := (15 * T / 4) * (1 / Real.pi) *
    (Real.log T * Real.exp (4 * C) * K * Real.sqrt (Real.pi / 80))
  have hbox : ∀ h ∈ Finset.Icc 1 ell, ∀ k ∈ Finset.Icc 1 ell,
      ‖hughesYoungFiniteDiagonalBox T (hughesYoungSmallContour T) H h k M M‖ ≤
        F * (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
          if h * m = k * n then
            ‖shortMobiusSquareCoeff T h‖ *
              ‖shortMobiusSquareCoeff T k‖ *
              (m.divisors.card : ℝ) * (n.divisors.card : ℝ) *
              (((h * m : ℕ) : ℝ))⁻¹
          else 0) := by
    intro h hh k hk
    have hhPos : 0 < h := (Finset.mem_Icc.mp hh).1
    have hkPos : 0 < k := (Finset.mem_Icc.mp hk).1
    unfold hughesYoungFiniteDiagonalBox
    calc
      ‖∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
          if quadraticDivisorShift h k m n = 0 then
            ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
              hughesYoungFiniteArithmeticTerm T t
                (hughesYoungSmallContour T) H h k (m, n)
          else 0‖ ≤
        ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
          ‖if quadraticDivisorShift h k m n = 0 then
            ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
              hughesYoungFiniteArithmeticTerm T t
                (hughesYoungSmallContour T) H h k (m, n)
          else 0‖ := by
            exact (norm_sum_le _ _).trans
              (Finset.sum_le_sum fun m _hm => norm_sum_le _ _)
      _ ≤ ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
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
            have hmPos : 0 < m := (Finset.mem_Icc.mp hm).1
            have hnPos : 0 < n := (Finset.mem_Icc.mp hn).1
            by_cases hdiag : h * m = k * n
            · have hshift : quadraticDivisorShift h k m n = 0 :=
                (quadraticDivisorShift_eq_zero_iff h k m n).2 hdiag
              rw [if_pos hshift, if_pos hdiag]
              have hb := hterm hT hH hhPos hkPos hmPos hnPos hdiag
              exact hb.trans_eq (by unfold F; ring)
            · have hshift : quadraticDivisorShift h k m n ≠ 0 := by
                exact fun hs => hdiag ((quadraticDivisorShift_eq_zero_iff h k m n).1 hs)
              simp [hdiag, hshift]
      _ = F * (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
          if h * m = k * n then
            ‖shortMobiusSquareCoeff T h‖ *
              ‖shortMobiusSquareCoeff T k‖ *
              (m.divisors.card : ℝ) * (n.divisors.card : ℝ) *
              (((h * m : ℕ) : ℝ))⁻¹
          else 0) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro m _hm
            rw [Finset.mul_sum]
  change ‖∑ h ∈ Finset.Icc 1 ell, ∑ k ∈ Finset.Icc 1 ell,
      hughesYoungFiniteDiagonalBox T (hughesYoungSmallContour T) H h k M M‖ ≤ _
  calc
    ‖∑ h ∈ Finset.Icc 1 ell, ∑ k ∈ Finset.Icc 1 ell,
        hughesYoungFiniteDiagonalBox T (hughesYoungSmallContour T) H h k M M‖ ≤
      ∑ h ∈ Finset.Icc 1 ell, ∑ k ∈ Finset.Icc 1 ell,
        ‖hughesYoungFiniteDiagonalBox T (hughesYoungSmallContour T) H h k M M‖ := by
          exact (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun h _hh => norm_sum_le _ _)
    _ ≤ ∑ h ∈ Finset.Icc 1 ell, ∑ k ∈ Finset.Icc 1 ell,
        F * (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
          if h * m = k * n then
            ‖shortMobiusSquareCoeff T h‖ *
              ‖shortMobiusSquareCoeff T k‖ *
              (m.divisors.card : ℝ) * (n.divisors.card : ℝ) *
              (((h * m : ℕ) : ℝ))⁻¹
          else 0) := by
            exact Finset.sum_le_sum fun h hh =>
              Finset.sum_le_sum fun k hk => hbox h hh k hk
    _ = F * hughesYoungFiniteDiagonalArithmeticMajorant T ell M := by
          unfold hughesYoungFiniteDiagonalArithmeticMajorant
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro h _hh
          rw [Finset.mul_sum]

/-- Fully arithmetic diagonal estimate for the literal finite rectangle.
All dependence on the truncation is now confined to an epsilon power and a
harmonic factor. -/
theorem exists_norm_hughesYoungFiniteDiagonalSum_le_power
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C K ca cd : ℝ,
      0 < C ∧ 0 < K ∧ 0 < ca ∧ 0 < cd ∧
      ∀ {T H : ℝ} {M : ℕ}, Real.exp 1 ≤ T → 0 ≤ H →
        ‖∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
            ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
              hughesYoungFiniteDiagonalBox T (hughesYoungSmallContour T)
                H h k M M‖ ≤
          ((15 * T / 4) * (1 / Real.pi) *
            (Real.log T * Real.exp (4 * C) * K *
              Real.sqrt (Real.pi / 80))) *
            ca ^ 2 * cd ^ 4 *
            (((detectorCutoff T) ^ 2 * M : ℕ) : ℝ) ^ (6 * δ) *
            (((harmonic (((detectorCutoff T) ^ 2 * M) : ℕ) : ℚ) : ℝ)) := by
  obtain ⟨C, K, hC, hK, hdiag⟩ :=
    exists_norm_hughesYoungFiniteDiagonalSum_le
  obtain ⟨ca, hca, hcoeff⟩ := shortMobiusSquareCoeff_bound δ hδ
  obtain ⟨cd, hcd, hdiv⟩ := divisorCountBound_native δ hδ
  refine ⟨C, K, ca, cd, hC, hK, hca, hcd, ?_⟩
  intro T H M hT hH
  let ell := (detectorCutoff T) ^ 2
  let cutoff := ell * M
  let F : ℝ := (15 * T / 4) * (1 / Real.pi) *
    (Real.log T * Real.exp (4 * C) * K * Real.sqrt (Real.pi / 80))
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hF0 : 0 ≤ F := by
    unfold F
    have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
    have hlog : 0 ≤ Real.log T := Real.log_nonneg hT1
    have hsqrt : 0 ≤ Real.sqrt (Real.pi / 80) := Real.sqrt_nonneg _
    positivity
  have hdiag' := hdiag (M := M) hT hH
  have hmajor := hughesYoungFiniteDiagonalArithmeticMajorant_le T ell M
  have hsmooth := smoothTwistedDiagonalMajorant_le
    (ell := ell) (cutoff := cutoff) hT0.le
    (shortMobiusSquareCoeff T) hδ.le hca.le hcd.le
    (fun h hh => hcoeff T h (Finset.mem_Icc.mp hh).1) hdiv
  have hsum :
      (∑ q ∈ Finset.Icc 1 cutoff,
        smoothTwistedDiagonalFiber ell q (shortMobiusSquareCoeff T) ^ 2 *
          (q : ℝ)⁻¹) ≤
        ca ^ 2 * cd ^ 4 * (cutoff : ℝ) ^ (6 * δ) *
          (((harmonic cutoff : ℚ) : ℝ)) := by
    unfold smoothTwistedDiagonalMajorant at hsmooth
    have hfactor : 0 < 5 * T / 2 := by positivity
    nlinarith
  change _ ≤ F * ca ^ 2 * cd ^ 4 * (cutoff : ℝ) ^ (6 * δ) *
    (((harmonic cutoff : ℚ) : ℝ))
  calc
    _ ≤ F * hughesYoungFiniteDiagonalArithmeticMajorant T ell M := by
      simpa only [F, ell] using hdiag'
    _ ≤ F * (∑ q ∈ Finset.Icc 1 cutoff,
        smoothTwistedDiagonalFiber ell q (shortMobiusSquareCoeff T) ^ 2 *
          (q : ℝ)⁻¹) := mul_le_mul_of_nonneg_left hmajor hF0
    _ ≤ F * (ca ^ 2 * cd ^ 4 * (cutoff : ℝ) ^ (6 * δ) *
        (((harmonic cutoff : ℚ) : ℝ))) := mul_le_mul_of_nonneg_left hsum hF0
    _ = _ := by ring

end RiemannZeta.GuthMaynard
