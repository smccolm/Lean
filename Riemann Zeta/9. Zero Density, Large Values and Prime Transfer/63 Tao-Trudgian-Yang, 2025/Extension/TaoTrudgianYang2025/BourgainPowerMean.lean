import TaoTrudgianYang2025.BourgainLocalMean

/-!
# A uniform small-power-window local mean for actual large-value patterns

The arbitrary-order Fourier tail is absorbed using only N^{-1} <= V.
This is a direct route to the mixed-moment lower bound on its allowed
small-power window; it does not assert the source's smaller log N window.
-/

open MeasureTheory RiemannZeta.GuthMaynard Set
open scoped Interval Classical

noncomputable section

namespace TaoTrudgianYang2025

/-- Fixed positive window exponent gives a genuine local L1 lower bound.
The constants precede the pattern and every ordinate. -/
theorem bourgain_power_window_local_mean {η : ℝ} (hη : 0 < η) :
    ∃ C N₀ : ℝ, 0 < C ∧ 2 ≤ N₀ ∧ ∀ P : LargeValuePattern,
      N₀ ≤ P.N → P.N^(-1 : ℝ) ≤ P.V →
      ∀ t ∈ P.ordinates,
        P.V ≤ C*(∫ u in -(2*Real.pi*P.N^η)..(2*Real.pi*P.N^η),
          ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n (t+u)‖) := by
  let q := Nat.ceil (3/η)+2
  have hq : 2 ≤ q := by dsimp only [q]; omega
  let D := gmAffineLocalBumpFourierTailConstant q hq
  have hD : 0 < D := gmAffineLocalBumpFourierTailConstant_pos q hq
  let K := gmAffineLocalBumpFourierSup/(2*Real.pi)
  have hK : 0 < K := div_pos gmAffineLocalBumpFourierSup_pos (by positivity)
  have hbudget : 3 ≤ η*((q : ℝ)-1) := by
    have hc := Nat.le_ceil (3/η)
    have hb := (div_le_iff₀ hη).mp hc
    dsimp only [q]
    push_cast
    nlinarith
  refine ⟨2*K, max 2 (4*D), by positivity, le_max_left _ _, ?_⟩
  intro P hP hV t ht
  have hN2 : 2 ≤ P.N := (le_max_left _ _).trans hP
  have hN1 : 1 ≤ P.N := by linarith
  have hN : 0 < P.N := by linarith
  have hDN : 4*D ≤ P.N := (le_max_right _ _).trans hP
  let H := P.N^η
  let R := 2*Real.pi*H
  let E := 2*P.N*D*H^(1-(q : ℝ))
  have hH : 1 ≤ H := Real.one_le_rpow hN1 hη.le
  have hR : 0 < R := by dsimp only [R]; positivity
  have hE : E ≤ 2*D*P.N^(-2 : ℝ) := by
    calc
      E = 2*D*P.N^(1+η*(1-(q : ℝ))) := by
        dsimp only [E, H]
        rw [← Real.rpow_mul hN.le, Real.rpow_add hN, Real.rpow_one]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith [hbudget])) (by positivity)
  have hdouble : 2*E ≤ P.N^(-1 : ℝ) := by
    calc
      _ ≤ 4*D*P.N^(-2 : ℝ) := by linarith
      _ ≤ P.N*P.N^(-2 : ℝ) :=
        mul_le_mul_of_nonneg_right hDN (Real.rpow_nonneg hN.le _)
      _ = _ := by
        calc
          P.N*P.N^(-2 : ℝ) = P.N^(1 : ℝ)*P.N^(-2 : ℝ) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hN]; norm_num
  have hm := bourgain_polynomial_local_mean_add_tail P t H hH q hq
  have hpoint := P.large t ht
  have hshift :
      (∫ y in Icc (t-R) (t+R), ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n y‖) =
      ∫ u in -R..R, ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n (t+u)‖ := by
    rw [intervalIntegral.integral_comp_add_left
        (f := fun y => ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n y‖),
      ← sub_eq_add_neg,
      intervalIntegral.integral_of_le (by linarith : t-R ≤ t+R),
      ← integral_Icc_eq_integral_Ioc]
  change ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n t‖ ≤
    K*(∫ y in Icc (t-R) (t+R), ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n y‖)+E at hm
  rw [hshift] at hm
  change P.V ≤ (2*K)*(∫ u in -R..R,
    ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n (t+u)‖)
  linarith

/-- The source physical large-value range discharges the local mean's
amplitude floor; no separate local-mean hypothesis is introduced. -/
theorem bourgain_power_window_local_mean_in_source_range {η : ℝ} (hη : 0 < η) :
    ∃ C N₀ : ℝ, 0 < C ∧ 2 ≤ N₀ ∧ ∀ P : LargeValuePattern,
      N₀ ≤ P.N → ∀ σ δ : ℝ, 0 ≤ σ → δ ≤ 1 → P.N^(σ-δ) ≤ P.V →
      ∀ t ∈ P.ordinates,
        P.V ≤ C*(∫ u in -(2*Real.pi*P.N^η)..(2*Real.pi*P.N^η),
          ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n (t+u)‖) := by
  obtain ⟨C, N₀, hC, hN₀, hm⟩ := bourgain_power_window_local_mean hη
  refine ⟨C, N₀, hC, hN₀, ?_⟩
  intro P hN σ δ hσ hδ hV
  apply hm P hN
  exact (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith : (-1 : ℝ) ≤ σ-δ)).trans hV

end TaoTrudgianYang2025
