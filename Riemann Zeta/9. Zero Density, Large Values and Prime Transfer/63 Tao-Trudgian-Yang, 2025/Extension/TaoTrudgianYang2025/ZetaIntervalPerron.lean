import TaoTrudgianYang2025.ZetaIntervalProbe
import TaoTrudgianYang2025.ZetaSixthPerron

/-! Literal sharp-interval Perron estimates, with all errors retained. -/

noncomputable section
open MeasureTheory
namespace TaoTrudgianYang2025

theorem zetaMomentConvolution_nonneg {T : ℝ} (hT : 0 ≤ T) (t : ℝ) :
    0 ≤ zetaMomentConvolution T t := by
  unfold zetaMomentConvolution
  exact intervalIntegral.integral_nonneg (by linarith)
    (fun u _ => mul_nonneg (zetaMomentKernel_pos t u).le (norm_nonneg _))

theorem norm_zetaInterval_le_sixth_convolution_and_errors
    (N : ℕ) (I : Finset ℕ) (T t : ℝ) (hN : 1 < N)
    (hI : IsIntegerInterval I) (hIN : I ⊆ Finset.Icc N (2*N))
    (hT : 0 < T) (ht : t ∈ Set.Icc T (2*T)) :
    ‖∑ n ∈ I, dirichletPhase n t‖ ≤
      zetaCutoffMellinConstant 1 (1/2)*Real.sqrt (N : ℝ)*zetaMomentConvolution T t+
      zetaCutoffMellinConstant 6 1*(N : ℝ)^6/(1+|t|)^6+
      240*zetaCutoffMellinConstant 6 (1/2)*(N : ℝ)^(11/2 : ℝ)/T^4 := by
  by_cases hz : ‖∑ n ∈ I, dirichletPhase n t‖ = 0
  · rw [hz]
    have := zetaCutoffMellinConstant_pos 1 (1/2)
    have := zetaCutoffMellinConstant_pos 6 1
    have := zetaCutoffMellinConstant_pos 6 (1/2)
    have := zetaMomentConvolution_nonneg hT.le t
    positivity
  have hp : 0 < ‖∑ n ∈ I, dirichletPhase n t‖ :=
    lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  obtain ⟨P,hPN,hPT,hPI,_hPV,htP⟩ :=
    exists_zetaIntervalProbe N I T t hN hI hIN hT ht hp
  obtain ⟨a,b,hab⟩ := hI
  have hactive : P.active = Finset.Icc a b := hPI.trans hab
  have he := P.polynomial_norm_le_sixth_convolution_and_errors hactive
    (P.active_nonempty_of_mem_ordinates htP) (by simpa only [hPT] using ht)
  simpa only [P.polynomial_eq_active_sum,hPI,hPN,hPT] using he

theorem norm_zetaInterval_le_sixth_convolution
    (N : ℕ) (I : Finset ℕ) (T t : ℝ) (hN : 1 < N)
    (hI : IsIntegerInterval I) (hIN : I ⊆ Finset.Icc N (2*N))
    (hscale : (N : ℝ)^(11/8 : ℝ) ≤ T) (ht : t ∈ Set.Icc T (2*T)) :
    ‖∑ n ∈ I, dirichletPhase n t‖ ≤
      zetaCutoffMellinConstant 1 (1/2)*Real.sqrt (N : ℝ)*zetaMomentConvolution T t+
      zetaSixthPerronError := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := zero_lt_one.trans hN1
  have hT : 0 < T := (Real.rpow_pos_of_pos hNp _).trans_le hscale
  have hNT : (N : ℝ) ≤ T := calc
    _ = (N : ℝ)^(1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ (N : ℝ)^(11/8 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hN1.le (by norm_num)
    _ ≤ T := hscale
  have hresPower : (N : ℝ)^6 ≤ (1+|t|)^6 :=
    pow_le_pow_left₀ hNp.le (by linarith [ht.1,le_abs_self t]) 6
  have hheightPower : (N : ℝ)^(11/2 : ℝ) ≤ T^4 := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hNp.le (11/8)) hscale 4
    have he : ((N : ℝ)^(11/8 : ℝ))^4 = (N : ℝ)^(11/2 : ℝ) := by
      rw [← Real.rpow_natCast _ 4,← Real.rpow_mul hNp.le]
      norm_num
    rwa [he] at hh
  have hres : zetaCutoffMellinConstant 6 1*(N : ℝ)^6/(1+|t|)^6 ≤
      zetaCutoffMellinConstant 6 1 := by
    apply (div_le_iff₀ (by positivity : 0 < (1+|t|)^6)).mpr
    exact mul_le_mul_of_nonneg_left hresPower (zetaCutoffMellinConstant_pos _ _).le
  have hfar : 240*zetaCutoffMellinConstant 6 (1/2)*(N : ℝ)^(11/2 : ℝ)/T^4 ≤
      240*zetaCutoffMellinConstant 6 (1/2) := by
    apply (div_le_iff₀ (pow_pos hT 4)).mpr
    exact mul_le_mul_of_nonneg_left hheightPower
      (mul_nonneg (by norm_num) (zetaCutoffMellinConstant_pos _ _).le)
  have hp := norm_zetaInterval_le_sixth_convolution_and_errors N I T t hN hI hIN hT ht
  unfold zetaSixthPerronError
  linarith

end TaoTrudgianYang2025
