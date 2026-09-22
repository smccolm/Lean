import TaoTrudgianYang2025.BetaQuadraticRemainder

/-!
# Local derivative budgets for the actual quadratic remainder

Only derivatives on the central interval are used. The actual globally
smooth weight is retained, so this can be applied where the original
cutoff is constant without paying its remote transition derivatives.
-/

noncomputable section

open Set Expdb MeasureTheory
open scoped ContDiff FourierTransform

namespace TaoTrudgianYang2025

theorem abs_segmentTaylorAverage_le_closed
    {f : ℝ → ℝ} {l r a x M : ℝ}
    (ha : a ∈ Icc l r) (hx : x ∈ Icc l r) (k : ℕ)
    (hb : ∀ u ∈ Icc l r, |iteratedDeriv k f u| ≤ M) :
    |segmentTaylorAverage f a k x| ≤ M := by
  have hpoint : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      ‖(1-t)*t^k*iteratedDeriv k f (a+t*(x-a))‖ ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hf : 0 ≤ (1-t)*t^k := mul_nonneg (by linarith [ht.2]) (pow_nonneg ht.1 k)
    have hf' : (1-t)*t^k ≤ 1 := by
      have hp : t^k ≤ 1 := pow_le_one₀ ht.1 ht.2
      nlinarith [mul_nonneg ht.1 (pow_nonneg ht.1 k)]
    have hseg : a+t*(x-a) ∈ Icc l r := by
      have h₁ := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr ha.1)
      have h₂ := mul_nonneg ht.1 (sub_nonneg.mpr hx.1)
      have h₃ := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr ha.2)
      have h₄ := mul_nonneg ht.1 (sub_nonneg.mpr hx.2)
      constructor <;> nlinarith
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg hf]
    exact (mul_le_of_le_one_left (norm_nonneg _) hf').trans (hb _ hseg)
  have h := norm_integral_le_of_norm_le_const hpoint
  simpa [segmentTaylorAverage,Real.norm_eq_abs,Measure.real] using h

theorem abs_quadraticTaylorCoefficient_le_local {W : ℝ → ℝ} {H M z : ℝ}
    (hH : 0 ≤ H) (hb : ∀ x ∈ Icc (-H) H, |iteratedDeriv 2 W x| ≤ M)
    (hz : z ∈ Icc (-H) H) :
    |quadraticTaylorCoefficient W z| ≤ M := by
  apply abs_segmentTaylorAverage_le_closed (show (0 : ℝ) ∈ Icc (-H) H by constructor <;> linarith) hz 0
  intro x hx
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hb x hx

theorem abs_deriv_quadraticTaylorCoefficient_le_local {W : ℝ → ℝ} {H M z : ℝ}
    (hW : ContDiff ℝ ∞ W) (hH : 0 ≤ H)
    (hb : ∀ x ∈ Icc (-H) H, |iteratedDeriv 3 W x| ≤ M)
    (hz : z ∈ Icc (-H) H) :
    |deriv (quadraticTaylorCoefficient W) z| ≤ M := by
  rw [quadraticTaylorCoefficient_deriv hW]
  apply abs_segmentTaylorAverage_le_closed (show (0 : ℝ) ∈ Icc (-H) H by constructor <;> linarith) hz 1
  intro x hx
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hb x hx

theorem norm_integral_sq_mul_betaQuadraticKernel_le_local
    {V : ℝ → ℝ} {T H M L : ℝ}
    (hV : ContDiff ℝ ∞ V) (hT : 0 < T) (hH : 0 < H)
    (hb : ∀ z ∈ Icc (-H) H, |V z| ≤ M)
    (hd : ∀ z ∈ Icc (-H) H, |deriv V z| ≤ L) :
    ‖∫ z in (-H)..H, ((z^2*V z : ℝ) : ℂ)*betaQuadraticKernel T z‖ ≤
      (2*H*M+2*H*(M+H*L))/(2*Real.pi*T) := by
  let c : ℂ := ((-2*Real.pi*T : ℝ) : ℂ)*Complex.I
  let U : ℝ → ℂ := fun z => ((z*V z : ℝ) : ℂ)
  let U' : ℝ → ℂ := fun z => ((V z+z*deriv V z : ℝ) : ℂ)
  have hDV : Continuous (deriv V) := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
      hV.continuous_iteratedDeriv 1 (by simp)
  have hU : ∀ z : ℝ, HasDerivAt U (U' z) z := by
    intro z
    have h := ((hasDerivAt_id z).mul
      (hV.differentiable (by simp : (∞ : WithTop ℕ∞) ≠ 0) z).hasDerivAt).ofReal_comp
    simpa only [id_eq,one_mul] using h
  have hK : ∀ z : ℝ, HasDerivAt (betaQuadraticKernel T)
      (c*(z : ℂ)*betaQuadraticKernel T z) z := by
    intro z
    convert betaQuadraticKernel_hasDerivAt T z using 1
    dsimp [c]
    push_cast
    ring
  have hUc : Continuous U' := Complex.continuous_ofReal.comp
    (hV.continuous.add (continuous_id.mul hDV))
  have hKc : Continuous (fun z : ℝ => c*(z : ℂ)*betaQuadraticKernel T z) :=
    (continuous_const.mul Complex.continuous_ofReal).mul (continuous_betaQuadraticKernel T)
  have hp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := U) (u' := U') (v := betaQuadraticKernel T)
    (v' := fun z : ℝ => c*(z : ℂ)*betaQuadraticKernel T z)
    (fun z _ => hU z) (fun z _ => hK z)
    (hUc.intervalIntegrable (-H) H) (hKc.intervalIntegrable (-H) H)
  have he : c*(∫ z in (-H)..H, ((z^2*V z : ℝ) : ℂ)*betaQuadraticKernel T z) =
      U H*betaQuadraticKernel T H-U (-H)*betaQuadraticKernel T (-H)-
        ∫ z in (-H)..H, U' z*betaQuadraticKernel T z := by
    rw [← hp,← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro z _
    dsimp [U]
    push_cast
    ring
  have hden : 0 < 2*Real.pi*T := mul_pos (mul_pos (by norm_num) Real.pi_pos) hT
  have hc : ‖c‖ = 2*Real.pi*T := by
    dsimp only [c]
    rw [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,
      abs_of_neg (by nlinarith : -2*Real.pi*T < 0)]
    ring
  have hUb : ∀ z : ℝ, |z| ≤ H → ‖U z*betaQuadraticKernel T z‖ ≤ H*M := by
    intro z hz
    rw [norm_mul,norm_betaQuadraticKernel,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_mul]
    exact mul_le_mul hz (hb z (abs_le.mp hz)) (abs_nonneg _) hH.le
  have hIb : ‖∫ z in (-H)..H, U' z*betaQuadraticKernel T z‖ ≤ 2*H*(M+H*L) := by
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -H) (b := H) (f := fun z : ℝ => U' z*betaQuadraticKernel T z) (C := M+H*L) (fun z hz => by
        have hz' : |z| ≤ H := by
          rw [uIoc_of_le (by linarith : -H ≤ H)] at hz
          exact abs_le.mpr ⟨hz.1.le,hz.2⟩
        rw [norm_mul,norm_betaQuadraticKernel,mul_one,Complex.norm_real,Real.norm_eq_abs]
        exact (abs_add_le (V z) (z*deriv V z)).trans
          (add_le_add (hb z (abs_le.mp hz')) (by
            rw [abs_mul]
            exact mul_le_mul hz' (hd z (abs_le.mp hz')) (abs_nonneg _) hH.le)))
    apply hbound.trans_eq
    rw [abs_of_nonneg (by linarith : 0 ≤ H- -H)]
    ring
  apply (le_div_iff₀ hden).mpr
  rw [mul_comm,← hc,← norm_mul,he]
  have hnorm := (norm_sub_le
    (U H*betaQuadraticKernel T H-U (-H)*betaQuadraticKernel T (-H))
    (∫ z in (-H)..H, U' z*betaQuadraticKernel T z)).trans
      (add_le_add (norm_sub_le _ _) le_rfl)
  have hright := hUb H (by rw [abs_of_pos hH])
  have hleft := hUb (-H) (by rw [abs_neg,abs_of_pos hH])
  linarith

theorem norm_quadratic_window_remainder_le_local
    {W : ℝ → ℝ} {T H M₀ M₂ M₃ : ℝ}
    (hW : ContDiff ℝ ∞ W) (hT : 0 < T) (hH : 0 < H)
    (h₀ : |W 0| ≤ M₀)
    (h₂ : ∀ z ∈ Icc (-H) H, |iteratedDeriv 2 W z| ≤ M₂)
    (h₃ : ∀ z ∈ Icc (-H) H, |iteratedDeriv 3 W z| ≤ M₃) :
    ‖(∫ z in (-H)..H, (W z : ℂ)*betaQuadraticKernel T z)-
      (W 0 : ℂ)*((𝐞 (-(1 : ℝ)/8) : ℂ)/(Real.sqrt T : ℂ))‖ ≤
        quadraticRemainderConstant H M₀ M₂ M₃/T := by
  have hparts := norm_integral_sq_mul_betaQuadraticKernel_le_local
    (quadraticTaylorCoefficient_contDiff hW) hT hH
    (fun z hz => abs_quadraticTaylorCoefficient_le_local hH.le h₂ hz)
    (fun z hz => abs_deriv_quadraticTaylorCoefficient_le_local hW hH.le h₃ hz)
  have htail := norm_betaQuadraticWindow_sub_main hT hH
  rw [integral_weighted_betaQuadraticKernel_taylor hW]
  have he :
      (W 0 : ℂ)*(∫ z in (-H)..H, betaQuadraticKernel T z)+
          (∫ z in (-H)..H, ((z^2*quadraticTaylorCoefficient W z : ℝ) : ℂ)*
            betaQuadraticKernel T z)-
          (W 0 : ℂ)*((𝐞 (-(1 : ℝ)/8) : ℂ)/(Real.sqrt T : ℂ)) =
      (W 0 : ℂ)*((∫ z in (-H)..H, betaQuadraticKernel T z)-
          (𝐞 (-(1 : ℝ)/8) : ℂ)/(Real.sqrt T : ℂ))+
          ∫ z in (-H)..H, ((z^2*quadraticTaylorCoefficient W z : ℝ) : ℂ)*
            betaQuadraticKernel T z := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  have hmain :
      ‖(W 0 : ℂ)*((∫ z in (-H)..H, betaQuadraticKernel T z)-
        (𝐞 (-(1 : ℝ)/8) : ℂ)/(Real.sqrt T : ℂ))‖ ≤ M₀*(4/(T*H*Real.pi)) := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul h₀ htail (norm_nonneg _) ((abs_nonneg _).trans h₀)
  apply (add_le_add hmain hparts).trans_eq
  unfold quadraticRemainderConstant
  field_simp

theorem quadraticRemainderConstant_le_inverse_window
    {H M₀ M₂ M₃ : ℝ} (hH : 0 < H) (hH₁ : H ≤ 1)
    (h₂ : 0 ≤ M₂) (h₃ : 0 ≤ M₃) :
    quadraticRemainderConstant H M₀ M₂ M₃ ≤
      (4*M₀/Real.pi+(4*M₂+2*M₃)/(2*Real.pi))/H := by
  have hH₂ : H^2 ≤ 1 := pow_le_one₀ hH.le hH₁
  have hH₃ : H^3 ≤ 1 := pow_le_one₀ hH.le hH₁
  have hb : 4*H^2*M₂+2*H^3*M₃ ≤ 4*M₂+2*M₃ := by
    nlinarith [mul_le_mul_of_nonneg_right hH₂ h₂,mul_le_mul_of_nonneg_right hH₃ h₃]
  apply (le_div_iff₀ hH).mpr
  have he : quadraticRemainderConstant H M₀ M₂ M₃*H =
      4*M₀/Real.pi+(4*H^2*M₂+2*H^3*M₃)/(2*Real.pi) := by
    unfold quadraticRemainderConstant
    field_simp
    ring
  rw [he]
  exact add_le_add le_rfl (div_le_div_of_nonneg_right hb (by positivity))

end TaoTrudgianYang2025
