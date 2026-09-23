import TaoTrudgianYang2025.SargosQuarticSharpCore
import TaoTrudgianYang2025.BetaFourierCarrierBounds

/-! Uniform second derivatives of the actual normalized quartic cutoff kernel. -/

noncomputable section

open Set Filter
open scoped ContDiff Topology FourierTransform

namespace TaoTrudgianYang2025

theorem sargosQuartic_normalized_slope_bound {ε u : ℝ}
    (hε : |ε| ≤ 1/96) (hu : u ∈ Icc (1:ℝ) 2) :
    |sargosQuarticSlope 1 ε u| ≤ 6 := by
  have hu₀ : 0 ≤ u := by linarith [hu.1]
  have hc := pow_le_pow_left₀ hu₀ hu.2 3
  unfold sargosQuarticSlope
  calc
    _ ≤ |2*1*u|+|4*ε*u^3| := abs_add_le _ _
    _ = 2*u+4*|ε| *u^3 := by
      rw [abs_mul,abs_mul,abs_mul,abs_pow,abs_of_nonneg hu₀]
      norm_num
    _ ≤ 2*2+4*(1/96)*2^3 := by
      have hh := mul_le_mul (mul_le_mul_of_nonneg_left hε (by norm_num : (0:ℝ) ≤ 4)) hc
        (pow_nonneg hu₀ 3) (by norm_num)
      linarith [hu.2]
    _ ≤ 6 := by norm_num

theorem sargosQuartic_normalized_secondDeriv_bound {ε u : ℝ}
    (hε : |ε| ≤ 1/96) (hu : u ∈ Icc (1:ℝ) 2) :
    |iteratedDeriv 2 (sargosQuarticPhase 1 ε) u| ≤ 6 := by
  have he : deriv (sargosQuarticPhase 1 ε) = sargosQuarticSlope 1 ε :=
    funext fun x => (sargosQuarticPhase_hasDerivAt 1 ε x).deriv
  change |iteratedDeriv (1+1) (sargosQuarticPhase 1 ε) u| ≤ 6
  rw [iteratedDeriv_succ',iteratedDeriv_one,he,(sargosQuarticSlope_hasDerivAt 1 ε u).deriv]
  have hc := sargosQuarticPhase_curvature
    (by norm_num : (0:ℝ) < 1) (by norm_num : (0:ℝ) < 1)
    (by simpa using hε) (by simpa only [mul_one] using hu)
  exact abs_le.mpr ⟨by linarith [hc.1],by linarith [hc.2]⟩

theorem sargosQuarticWeightedKernel_normalized (χ : ℝ → ℝ) (T ε u : ℝ) :
    sargosQuarticWeightedKernel χ 1 T (T*ε) u =
      (χ u : ℂ)*(𝐞 (T*sargosQuarticPhase 1 ε u) : ℂ) := by
  simp only [sargosQuarticWeightedKernel,div_one]
  rw [show sargosQuarticPhase T (T*ε) u = T*sargosQuarticPhase 1 ε u by
    unfold sargosQuarticPhase
    ring]

theorem sargosQuarticBufferedKernel_norm_le_one (l b η N α γ x : ℝ) :
    ‖sargosQuarticWeightedKernel (modelPhaseBufferedCutoff l b η) N α γ x‖ ≤ 1 := by
  simp only [sargosQuarticWeightedKernel,norm_mul,Circle.norm_coe,mul_one,
    Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (modelPhaseBufferedCutoff_nonneg _ _ _ _)]
  exact modelPhaseBufferedCutoff_le_one _ _ _ _

theorem sargosQuarticBufferedKernel_uniform_second_derivative :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l b η : ℝ), 1 ≤ l → b ≤ 2 → 0 < η → η ≤ 1 →
      ∀ (ε T : ℝ), |ε| ≤ 1/96 →
      ∀ u : ℝ,
        ‖iteratedDeriv 2 (sargosQuarticWeightedKernel
          (modelPhaseBufferedCutoff l b η) 1 T (T*ε)) u‖ ≤ C*(η⁻¹)^2*(1+|T|)^2 := by
  obtain ⟨M,hM,hcut⟩ := modelPhaseBufferedCutoff_uniform_c2
  let D : ℝ := (2*Real.pi)^2*6^2+2*Real.pi*6+1
  have hD : 1 ≤ D := by
    have hh : 0 ≤ (2*Real.pi)^2*6^2+2*Real.pi*6 := by positivity
    dsimp [D]
    linarith
  refine ⟨4*M*D,by nlinarith [mul_le_mul hM hD (by norm_num) (by linarith : 0 ≤ M)],?_⟩
  intro l b η hl hb hη hη₁ ε T hε u
  let χ := modelPhaseBufferedCutoff l b η
  have heq : sargosQuarticWeightedKernel χ 1 T (T*ε) =
      fun x => (χ x : ℂ)*(𝐞 (T*sargosQuarticPhase 1 ε x) : ℂ) :=
    funext fun x => sargosQuarticWeightedKernel_normalized χ T ε x
  by_cases hu : u ∈ tsupport χ
  · have hu' : u ∈ Ioo (1:ℝ) 2 := modelPhaseBufferedCutoff_tsupport_model hη hl hb hu
    have huc : u ∈ Icc (1:ℝ) 2 := ⟨hu'.1.le,hu'.2.le⟩
    have hphase := intervalC2Bound_fourierChar_of_derivative_bounds
      (F := sargosQuarticPhase 1 ε) (a := u) (b := u) (K := 6) (by norm_num)
      (fun _ _ => (contDiff_sargosQuarticPhase 1 ε).contDiffAt.of_le
        (by decide : (2 : WithTop ℕ∞) ≤ ∞))
      (fun x hx => by
        have hx' : x = u := le_antisymm hx.2 hx.1
        subst x
        rw [(sargosQuarticPhase_hasDerivAt 1 ε u).deriv]
        exact sargosQuartic_normalized_slope_bound hε huc)
      (fun x hx => by
        have hx' : x = u := le_antisymm hx.2 hx.1
        subst x
        exact sargosQuartic_normalized_secondDeriv_bound hε huc) T
    have hA : 1 ≤ η⁻¹ := (one_le_inv₀ hη).mpr hη₁
    have hR₁ : η⁻¹ ≤ η⁻¹*(1+|T|) :=
      le_mul_of_one_le_right (by positivity) (by linarith [abs_nonneg T])
    have hR₂ : 1+|T| ≤ η⁻¹*(1+|T|) :=
      le_mul_of_one_le_left (by positivity) hA
    have hp := ((hcut l b η u u hη).mono le_rfl hR₁).mul (hphase.mono le_rfl hR₂)
    rw [heq]
    convert hp.second_le u ⟨le_rfl,le_rfl⟩ using 1
    dsimp [χ,D]
    ring
  · have hz : sargosQuarticWeightedKernel χ 1 T (T*ε) =ᶠ[𝓝 u] fun _ => (0 : ℂ) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hu] with x hx
      simp only [sargosQuarticWeightedKernel,div_one,hx,Pi.zero_apply,Complex.ofReal_zero,zero_mul]
    rw [hz.iteratedDeriv_eq 2]
    simp only [iteratedDeriv_const,show (2:ℕ) ≠ 0 by norm_num,if_false,norm_zero]
    have hM₀ : 0 ≤ M := by linarith
    have hD₀ : 0 ≤ D := by linarith
    positivity

end TaoTrudgianYang2025
