import TaoTrudgianYang2025.ZetaTwelfthGlobal
import TaoTrudgianYang2025.ZetaIntervalPerron

/-! A common convolution window for separated samples at all positive heights. -/

noncomputable section
open Filter MeasureTheory
namespace TaoTrudgianYang2025

def zetaGlobalConvolution (T t : ℝ) : ℝ :=
  ∫ u in 0..3*T, zetaMomentKernel t u*zetaMomentCriticalNorm u

theorem zetaGlobalConvolution_nonneg {T : ℝ} (hT : 0 ≤ T) (t : ℝ) :
    0 ≤ zetaGlobalConvolution T t := by
  unfold zetaGlobalConvolution
  exact intervalIntegral.integral_nonneg (by linarith)
    (fun u _ => mul_nonneg (zetaMomentKernel_pos t u).le (norm_nonneg _))

theorem zetaMomentConvolution_le_global {T t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    zetaMomentConvolution t t ≤ zetaGlobalConvolution T t := by
  unfold zetaMomentConvolution zetaGlobalConvolution
  apply intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
  · exact Eventually.of_forall fun u =>
      mul_nonneg (zetaMomentKernel_pos t u).le (norm_nonneg _)
  · exact ((continuous_zetaMomentKernel t).mul continuous_zetaMomentCriticalNorm).intervalIntegrable _ _

theorem sum_zetaMomentKernel_on_global_window
    {T u : ℝ} (W : Finset ℝ) (hT : 0 < T) (hsep : IsOneSeparated W)
    (hW : ∀ t ∈ W, t ∈ Set.Icc 0 T) (hu : u ∈ Set.Icc 0 (3*T)) :
    (∑ t ∈ W, zetaMomentKernel t u) ≤ zetaMomentLogLoss (2*T) := by
  unfold zetaMomentLogLoss
  have he : 2*(2*T) = 4*T := by ring
  rw [he]
  apply sum_zetaMomentKernel_le_log W u (Nat.ceil (4*T)) hsep
  intro t ht
  have hb := hW t ht
  have hc : 4*T ≤ (Nat.ceil (4*T) : ℝ) := Nat.le_ceil _
  apply abs_le.mpr
  constructor <;> linarith [hu.1,hu.2,hb.1,hb.2]

theorem integral_zetaMomentKernel_global_mass
    {T t : ℝ} (hT : 0 < T) (ht : t ∈ Set.Icc 0 T) :
    0 < (∫ u in 0..3*T, zetaMomentKernel t u) ∧
      (∫ u in 0..3*T, zetaMomentKernel t u) ≤ zetaMomentLogLoss (2*T) := by
  constructor
  · apply intervalIntegral.integral_pos (by linarith)
      (continuous_zetaMomentKernel t).continuousOn
    · intro u _
      exact (zetaMomentKernel_pos t u).le
    · exact ⟨T,⟨by linarith,by linarith⟩,zetaMomentKernel_pos t T⟩
  · rw [integral_zetaMomentKernel ht.1 (by linarith [ht.2])]
    have hc : 2*(2*T) ≤ (Nat.ceil (2*(2*T)) : ℝ) := Nat.le_ceil _
    have hl := Real.log_le_log (by linarith [ht.1] : 0 < 1+t-0)
      (by linarith [ht.2] : 1+t-0 ≤ (Nat.ceil (2*(2*T)) : ℝ)+1)
    have hr := Real.log_le_log (by linarith [ht.2] : 0 < 1+3*T-t)
      (by linarith [ht.1] : 1+3*T-t ≤ (Nat.ceil (2*(2*T)) : ℝ)+1)
    unfold zetaMomentLogLoss
    linarith

theorem sum_global_convolution_twelfth_le_moment
    {T : ℝ} (W : Finset ℝ) (hT : 0 < T) (hsep : IsOneSeparated W)
    (hW : ∀ t ∈ W, t ∈ Set.Icc 0 T)
    (f : ℝ → ℝ) (hf : Continuous f) (hf0 : ∀ u, 0 ≤ f u) :
    (∑ t ∈ W, (∫ u in 0..3*T, zetaMomentKernel t u*f u)^12) ≤
      zetaMomentLogLoss (2*T)^12*(∫ u in 0..3*T, f u^12) := by
  have hab : (0 : ℝ) ≤ 3*T := by linarith
  have hweighted (t : ℝ) : Continuous (fun u => zetaMomentKernel t u*f u^12) :=
    (continuous_zetaMomentKernel t).mul (hf.pow 12)
  have hJensen (t : ℝ) (ht : t ∈ W) :
      (∫ u in 0..3*T, zetaMomentKernel t u*f u)^12 ≤
        zetaMomentLogLoss (2*T)^11*(∫ u in 0..3*T, zetaMomentKernel t u*f u^12) := by
    obtain ⟨hmass,hbound⟩ := integral_zetaMomentKernel_global_mass hT (hW t ht)
    have hr := integral_weighted_twelfth (μ:=volume.restrict (Set.Ioc 0 (3*T)))
      (fun u => (zetaMomentKernel_pos t u).le) hf0
      ((continuous_zetaMomentKernel t).intervalIntegrable 0 (3*T)).1
      (((continuous_zetaMomentKernel t).mul hf).intervalIntegrable 0 (3*T)).1
      ((hweighted t).intervalIntegrable 0 (3*T)).1
      (by simpa only [intervalIntegral.integral_of_le hab] using hmass)
    have hr' : (∫ u in 0..3*T, zetaMomentKernel t u*f u)^12 ≤
        (∫ u in 0..3*T, zetaMomentKernel t u)^11*
          (∫ u in 0..3*T, zetaMomentKernel t u*f u^12) := by
      simpa only [intervalIntegral.integral_of_le hab] using hr
    apply hr'.trans
    apply mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hmass.le hbound 11)
    exact intervalIntegral.integral_nonneg hab fun u _ =>
      mul_nonneg (zetaMomentKernel_pos t u).le (pow_nonneg (hf0 u) 12)
  have hsum : (∑ t ∈ W, ∫ u in 0..3*T, zetaMomentKernel t u*f u^12) ≤
      zetaMomentLogLoss (2*T)*(∫ u in 0..3*T, f u^12) := by
    rw [← intervalIntegral.integral_finsetSum (fun t _ =>
      (hweighted t).intervalIntegrable 0 (3*T)),← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hab
      ((continuous_finsetSum W fun t _ => hweighted t).intervalIntegrable 0 (3*T))
      (((hf.pow 12).const_mul _).intervalIntegrable 0 (3*T))
    intro u hu
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right
      (sum_zetaMomentKernel_on_global_window W hT hsep hW hu) (pow_nonneg (hf0 u) 12)
  calc
    _ ≤ ∑ t ∈ W, zetaMomentLogLoss (2*T)^11*
        (∫ u in 0..3*T, zetaMomentKernel t u*f u^12) := Finset.sum_le_sum hJensen
    _ = zetaMomentLogLoss (2*T)^11*
        (∑ t ∈ W, ∫ u in 0..3*T, zetaMomentKernel t u*f u^12) := (Finset.mul_sum ..).symm
    _ ≤ zetaMomentLogLoss (2*T)^11*
        (zetaMomentLogLoss (2*T)*(∫ u in 0..3*T, f u^12)) :=
      mul_le_mul_of_nonneg_left hsum (pow_nonneg (zetaMomentLogLoss_pos _).le 11)
    _ = _ := by ring

theorem exists_sum_zetaGlobalConvolution_twelfth_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧ ∀ (T : ℝ) (W : Finset ℝ),
      T₀ ≤ T → IsOneSeparated W → (∀ t ∈ W, t ∈ Set.Icc 0 T) →
      (∑ t ∈ W, zetaGlobalConvolution T t^12) ≤ C*T^(2+ε) := by
  obtain ⟨C,T₀,hC,hT₀,hglobal⟩ := exists_zeta_global_twelfth_log_bound hε
  refine ⟨C,T₀,hC,hT₀,?_⟩
  intro T W hT hsep hW
  exact (sum_global_convolution_twelfth_le_moment W (by linarith) hsep hW
    zetaMomentCriticalNorm continuous_zetaMomentCriticalNorm (fun _ => norm_nonneg _)).trans
      (hglobal T hT)

end TaoTrudgianYang2025

