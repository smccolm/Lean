import TaoTrudgianYang2025.AtkinsonStationaryTails

/-!
# Full actual carrier reduced to a finite quadratic stationary integral

The public theorem starts at the actual positive-support source integral.
It combines the constructed variation tails and natural-scale local error.
No Fresnel value, sharp source-scale truncation, or moment bound is assumed.
-/

noncomputable section

open Complex MeasureTheory Set

namespace TaoTrudgianYang2025

theorem IntervalC2Bound.atkinsonQuadraticApproximation {f : ℝ → ℂ}
    {a c M R T H : ℝ} (hf : IntervalC2Bound f a c M R)
    (hv : IntervalC1Bound f a c M) (hT : 0 < T) (b : ℝ)
    (ha : 0 < a) (hH : 0 < H)
    (hleft : a ≤ atkinsonSaddleRoot (T / (2 * Real.pi)) b - H)
    (hright : atkinsonSaddleRoot (T / (2 * Real.pi)) b + H ≤ c)
    (hwindow : H ≤ atkinsonSaddleRoot (T / (2 * Real.pi)) b / 2) :
    ‖(∫ y in a..c, f y * atkinsonRootKernel T b y) -
      f (atkinsonSaddleRoot (T / (2 * Real.pi)) b) *
        ∫ y in (atkinsonSaddleRoot (T / (2 * Real.pi)) b - H)..
          (atkinsonSaddleRoot (T / (2 * Real.pi)) b + H), atkinsonRootQuadraticKernel T b y‖ ≤
      M * (2 / (H * Real.pi) + 2 * R * H ^ 2 + 8 * T * H ^ 4 /
        (atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 3) := by
  have hlocal := hf.atkinsonLocalQuadratic hT b hH.le hleft hright hwindow
  have htail := hv.atkinsonRoot_sub_local hT b ha hH hleft hright
  apply (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans ((add_le_add htail hlocal).trans_eq ?_)
  ring

theorem exists_intervalC1Bound_atkinsonPowerWeight_root (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 0 < T → 0 < G → G ^ 2 ≤ 2 * T → 0 < L →
      IntervalC1Bound (fun y => atkinsonPowerWeight T G L α (y ^ 2))
        (Real.sqrt T / 4) (Real.sqrt T) (C * G * T ^ (-α)) := by
  obtain ⟨C, hC, hbound⟩ := exists_intervalC1Bound_atkinsonPowerWeight α
  refine ⟨C, hC, ?_⟩
  intro T G L hT hG hGT hL
  have hsq : (Real.sqrt T / 4) ^ 2 = T / 16 := by
    rw [div_pow, Real.sq_sqrt hT.le]
    norm_num
  have hf : IntervalC1Bound (atkinsonPowerWeight T G L α)
      ((Real.sqrt T / 4) ^ 2) ((Real.sqrt T) ^ 2) (C * G * T ^ (-α)) := by
    rw [hsq, Real.sq_sqrt hT.le]
    exact hbound T G L hT hG hGT hL
  exact hf.comp_sq (by positivity) (by nlinarith [Real.sqrt_nonneg T])

theorem exists_atkinsonPowerIntegral_quadratic_approximation (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L b H : ℝ, 0 < T → 1 ≤ G → G ^ 2 ≤ 2 * T →
      1 ≤ L → 8 * L ≤ G → 0 < H →
      Real.sqrt T / 4 ≤ atkinsonSaddleRoot (T / (2 * Real.pi)) b - H →
      atkinsonSaddleRoot (T / (2 * Real.pi)) b + H ≤ Real.sqrt T →
      H ≤ atkinsonSaddleRoot (T / (2 * Real.pi)) b / 2 →
      ‖atkinsonPowerIntegral T G L α b -
        2 * atkinsonPowerWeight T G L α ((atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 2) *
          ∫ y in (atkinsonSaddleRoot (T / (2 * Real.pi)) b - H)..
            (atkinsonSaddleRoot (T / (2 * Real.pi)) b + H), atkinsonRootQuadraticKernel T b y‖ ≤
        C * G * T ^ (-α) * (4 / (H * Real.pi) + 4 * (G / Real.sqrt T) * H ^ 2 +
          16 * T * H ^ 4 / (atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 3) := by
  obtain ⟨A, hA, hv⟩ := exists_intervalC1Bound_atkinsonPowerWeight_root α
  obtain ⟨B, hB, hf⟩ := exists_intervalC2Bound_atkinsonPowerWeight_root_natural α
  refine ⟨A + B, by positivity, ?_⟩
  intro T G L b H hT hG hGT hL hwidth hH hleft hright hwindow
  have hG0 : 0 < G := by linarith
  have hL0 : 0 < L := by linarith
  have hAM : A * G * T ^ (-α) ≤ (A + B) * G * T ^ (-α) := by gcongr; linarith
  have hBM : B * G * T ^ (-α) ≤ (A + B) * G * T ^ (-α) := by gcongr; linarith
  have h := ((hf T G L hT hG hGT hL hwidth).mono hBM le_rfl).atkinsonQuadraticApproximation
    ((hv T G L hT hG0 hGT hL0).mono hAM) hT b (by positivity) hH hleft hright hwindow
  have hs : Real.sqrt (T / 16) = Real.sqrt T / 4 := by
    rw [Real.sqrt_div hT.le]
    norm_num
  rw [atkinsonPowerIntegral_eq_root hT hG0 hL0 hwidth α b, hs]
  have he (x y z : ℂ) : 2 * x - 2 * y * z = 2 * (x - y * z) := by ring
  rw [he, norm_mul, Complex.norm_ofNat]
  apply (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)).trans_eq
  ring

end TaoTrudgianYang2025

