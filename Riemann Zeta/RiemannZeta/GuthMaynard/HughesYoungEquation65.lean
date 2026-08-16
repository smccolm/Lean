import RiemannZeta.GuthMaynard.HughesYoungPolynomialRatioJets
import RiemannZeta.GuthMaynard.HughesYoungCutoff

open Complex Filter MeasureTheory Set Topology
open Classical
open scoped ContDiff

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Hughes--Young equation (65)

This file proves the physical-height derivative estimates needed for the
repeated integration by parts in Hughes--Young equation (65).  The proof uses
the exact factorization of the shifted contour weight, Cauchy estimates for
the pole-cancelling rational factor, and the paired-Gamma logarithmic jets.
-/

/-- The order-`n` Leibniz constant for the product of the rational factor and
the paired Gamma quotient. -/
noncomputable def hughesYoungRightContourDerivativeConstant (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    n.choose i * (i.factorial * 6 ^ (8 : ℕ)) *
      hughesYoungGammaRatioBellConstant (n - i)

theorem hughesYoungRightContourDerivativeConstant_pos (n : ℕ) :
    0 < hughesYoungRightContourDerivativeConstant n := by
  unfold hughesYoungRightContourDerivativeConstant
  apply Finset.sum_pos'
  · intro i hi
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (by positivity)))
      (hughesYoungGammaRatioBellConstant_nonneg _)
  · refine ⟨n, by simp, ?_⟩
    simp
    positivity

/-- Exact all-orders physical-height derivative formula for the complete
right-contour coefficient. -/
theorem iteratedDeriv_hughesYoungRightContourWeight_shift_eq
    (n : ℕ) {c : ℝ} (hc : 0 < c) (u t : ℝ) :
    iteratedDeriv n (fun x : ℝ =>
        hughesYoungRightContourWeight x c u) t =
      (Complex.exp (100 * (((c : ℂ) + (u : ℂ) * I) ^ 2)) /
          ((c : ℂ) + (u : ℂ) * I)) *
        (∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℂ) *
            iteratedDeriv i (fun x : ℝ =>
              hughesYoungPolynomialRatioShift x c u) t *
            iteratedDeriv (n - i) (fun x : ℝ =>
              hughesYoungGammaRatioShift x c u) t) := by
  let A : ℂ :=
    Complex.exp (100 * (((c : ℂ) + (u : ℂ) * I) ^ 2)) /
      ((c : ℂ) + (u : ℂ) * I)
  let P : ℝ → ℂ := fun x => hughesYoungPolynomialRatioShift x c u
  let G : ℝ → ℂ := fun x => hughesYoungGammaRatioShift x c u
  have hfun : (fun x : ℝ => hughesYoungRightContourWeight x c u) =
      fun x : ℝ => A * (P x * G x) := by
    funext x
    rw [hughesYoungRightContourWeight_shift_eq]
    dsimp [A, P, G]
    ring
  rw [hfun, iteratedDeriv_const_mul_field]
  change A * iteratedDeriv n (P * G) t = _
  rw [iteratedDeriv_mul
    ((contDiff_hughesYoungPolynomialRatioShift c u).contDiffAt.of_le
      (by exact_mod_cast le_top))
    ((contDiff_hughesYoungGammaRatioShift (by linarith) u).contDiffAt.of_le
      (by exact_mod_cast le_top))]

private theorem norm_hughesYoungRightContour_constant_le
    {c u : ℝ} (hc : 0 < c) :
    ‖Complex.exp (100 * (((c : ℂ) + (u : ℂ) * I) ^ 2)) /
        ((c : ℂ) + (u : ℂ) * I)‖ ≤
      c⁻¹ * Real.exp (100 * c ^ 2 - 100 * u ^ 2) := by
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  have hw : c ≤ ‖w‖ := by
    have hre := Complex.abs_re_le_norm w
    simpa [w, abs_of_pos hc] using hre
  have hwpos : 0 < ‖w‖ := hc.trans_le hw
  have hgauss : ‖Complex.exp (100 * w ^ 2)‖ =
      Real.exp (100 * c ^ 2 - 100 * u ^ 2) := by
    rw [Complex.norm_exp]
    congr 1
    simp [w, pow_two, Complex.mul_re]
    ring
  change ‖Complex.exp (100 * w ^ 2) / w‖ ≤ _
  rw [norm_div, hgauss]
  have hinv : 1 / ‖w‖ ≤ c⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hc hw
  calc
    Real.exp (100 * c ^ 2 - 100 * u ^ 2) / ‖w‖ =
        Real.exp (100 * c ^ 2 - 100 * u ^ 2) * (1 / ‖w‖) := by ring
    _ ≤ Real.exp (100 * c ^ 2 - 100 * u ^ 2) * c⁻¹ := by
      exact mul_le_mul_of_nonneg_left hinv (Real.exp_nonneg _)
    _ = c⁻¹ * Real.exp (100 * c ^ 2 - 100 * u ^ 2) := by ring

/-- Uniform all-orders physical-height derivative bound for the complete
right-contour coefficient in the central Mellin range. -/
theorem exists_norm_iteratedDeriv_hughesYoungRightContourWeight_shift_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (T t c u : ℝ),
      16 ≤ T → T / 4 ≤ t → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      ‖iteratedDeriv n (fun x : ℝ =>
          hughesYoungRightContourWeight x c u) t‖ ≤
        c⁻¹ * Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * C * c * Real.log (|t| + |u| + 2)) *
          hughesYoungRightContourDerivativeConstant n *
          (((T / 16)⁻¹ * (1 + |u|)) ^ n) := by
  obtain ⟨C, hC, hgamma⟩ :=
    exists_norm_iteratedDeriv_hughesYoungGammaRatioShift_le
  refine ⟨C, hC, ?_⟩
  intro n T t c u hT ht hc hc1 hu
  let S : ℝ := (T / 16)⁻¹ * (1 + |u|)
  let E : ℝ := Real.exp
    (4 * C * c * Real.log (|t| + |u| + 2) + 16 * u ^ 2)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hA := norm_hughesYoungRightContour_constant_le (u := u) hc
  rw [iteratedDeriv_hughesYoungRightContourWeight_shift_eq n hc u t,
    norm_mul]
  calc
    ‖Complex.exp (100 * (((c : ℂ) + (u : ℂ) * I) ^ 2)) /
          ((c : ℂ) + (u : ℂ) * I)‖ *
        ‖∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℂ) *
            iteratedDeriv i (fun x : ℝ =>
              hughesYoungPolynomialRatioShift x c u) t *
            iteratedDeriv (n - i) (fun x : ℝ =>
              hughesYoungGammaRatioShift x c u) t‖ ≤
        (c⁻¹ * Real.exp (100 * c ^ 2 - 100 * u ^ 2)) *
          (∑ i ∈ Finset.range (n + 1),
            (n.choose i * (i.factorial * 6 ^ (8 : ℕ)) *
              hughesYoungGammaRatioBellConstant (n - i)) *
                E * S ^ n) := by
      apply mul_le_mul hA
      · calc
          ‖∑ i ∈ Finset.range (n + 1),
              (n.choose i : ℂ) *
                iteratedDeriv i (fun x : ℝ =>
                  hughesYoungPolynomialRatioShift x c u) t *
                iteratedDeriv (n - i) (fun x : ℝ =>
                  hughesYoungGammaRatioShift x c u) t‖ ≤
              ∑ i ∈ Finset.range (n + 1),
                ‖(n.choose i : ℂ) *
                  iteratedDeriv i (fun x : ℝ =>
                    hughesYoungPolynomialRatioShift x c u) t *
                  iteratedDeriv (n - i) (fun x : ℝ =>
                    hughesYoungGammaRatioShift x c u) t‖ :=
            norm_sum_le _ _
          _ ≤ ∑ i ∈ Finset.range (n + 1),
                (n.choose i * (i.factorial * 6 ^ (8 : ℕ)) *
                  hughesYoungGammaRatioBellConstant (n - i)) *
                    E * S ^ n := by
            apply Finset.sum_le_sum
            intro i hi
            have hiN : i ≤ n :=
              Nat.le_of_lt_succ (Finset.mem_range.mp hi)
            have hP :=
              norm_iteratedDeriv_hughesYoungPolynomialRatioShift_le_commonScale
                i hT ht hc.le hc1 hu
            have hG := hgamma (n - i) T t c u hT ht hc.le hc1 hu
            change ‖iteratedDeriv i (fun x : ℝ =>
                hughesYoungPolynomialRatioShift x c u) t‖ ≤
              (i.factorial * 6 ^ (8 : ℕ)) * S ^ i at hP
            change ‖iteratedDeriv (n - i) (fun x : ℝ =>
                hughesYoungGammaRatioShift x c u) t‖ ≤
              E * hughesYoungGammaRatioBellConstant (n - i) *
                S ^ (n - i) at hG
            rw [norm_mul, norm_mul, Complex.norm_natCast]
            calc
              (n.choose i : ℝ) *
                    ‖iteratedDeriv i (fun x : ℝ =>
                      hughesYoungPolynomialRatioShift x c u) t‖ *
                    ‖iteratedDeriv (n - i) (fun x : ℝ =>
                      hughesYoungGammaRatioShift x c u) t‖ ≤
                  (n.choose i : ℝ) *
                    ((i.factorial * 6 ^ (8 : ℕ)) * S ^ i) *
                    (E * hughesYoungGammaRatioBellConstant (n - i) *
                      S ^ (n - i)) := by
                have hchoose : 0 ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
                have hleft := mul_le_mul_of_nonneg_left hP hchoose
                exact mul_le_mul hleft hG (norm_nonneg _)
                  (mul_nonneg hchoose
                    (mul_nonneg (by positivity) (pow_nonneg hS _)))
              _ = (n.choose i * (i.factorial * 6 ^ (8 : ℕ)) *
                    hughesYoungGammaRatioBellConstant (n - i)) *
                      E * S ^ n := by
                have hpow : S ^ i * S ^ (n - i) = S ^ n := by
                  rw [← pow_add, Nat.add_sub_of_le hiN]
                calc
                  (n.choose i : ℝ) *
                        ((i.factorial * 6 ^ (8 : ℕ)) * S ^ i) *
                        (E * hughesYoungGammaRatioBellConstant (n - i) *
                          S ^ (n - i)) =
                      (n.choose i * (i.factorial * 6 ^ (8 : ℕ)) *
                        hughesYoungGammaRatioBellConstant (n - i)) * E *
                          (S ^ i * S ^ (n - i)) := by ring
                  _ = _ := by rw [hpow]
      · positivity
      · positivity
    _ = c⁻¹ * Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * C * c * Real.log (|t| + |u| + 2)) *
          hughesYoungRightContourDerivativeConstant n * S ^ n := by
      have hsum :
          (∑ i ∈ Finset.range (n + 1),
            (n.choose i * (i.factorial * 6 ^ (8 : ℕ)) *
              hughesYoungGammaRatioBellConstant (n - i)) * E * S ^ n) =
          (∑ i ∈ Finset.range (n + 1),
            n.choose i * (i.factorial * 6 ^ (8 : ℕ)) *
              hughesYoungGammaRatioBellConstant (n - i)) * E * S ^ n := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
      rw [hsum]
      dsimp only [hughesYoungRightContourDerivativeConstant, E]
      let D : ℝ := ∑ i ∈ Finset.range (n + 1),
        n.choose i * (i.factorial * 6 ^ (8 : ℕ)) *
          hughesYoungGammaRatioBellConstant (n - i)
      have hexp :
          Real.exp (100 * c ^ 2 - 100 * u ^ 2) *
              Real.exp
                (4 * C * c * Real.log (|t| + |u| + 2) + 16 * u ^ 2) =
            Real.exp
              (100 * c ^ 2 - 84 * u ^ 2 +
                4 * C * c * Real.log (|t| + |u| + 2)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      change c⁻¹ * Real.exp (100 * c ^ 2 - 100 * u ^ 2) *
          (D * Real.exp
            (4 * C * c * Real.log (|t| + |u| + 2) + 16 * u ^ 2) *
              S ^ n) =
        c⁻¹ * Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * C * c * Real.log (|t| + |u| + 2)) * D * S ^ n
      calc
        c⁻¹ * Real.exp (100 * c ^ 2 - 100 * u ^ 2) *
            (D * Real.exp
              (4 * C * c * Real.log (|t| + |u| + 2) + 16 * u ^ 2) *
                S ^ n) =
            c⁻¹ *
              (Real.exp (100 * c ^ 2 - 100 * u ^ 2) *
                Real.exp
                  (4 * C * c * Real.log (|t| + |u| + 2) + 16 * u ^ 2)) *
              D * S ^ n := by ring
        _ = _ := by rw [hexp]
    _ = _ := rfl

end RiemannZeta.GuthMaynard
