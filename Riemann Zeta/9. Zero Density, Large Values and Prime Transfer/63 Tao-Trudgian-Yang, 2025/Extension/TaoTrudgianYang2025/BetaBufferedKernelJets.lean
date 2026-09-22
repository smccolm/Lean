import TaoTrudgianYang2025.BetaFourierCarrierBounds
import TaoTrudgianYang2025.BetaTaylorJets
import TaoTrudgianYang2025.BetaFourierModes

/-!
# Uniform second derivatives of the original normalized Poisson kernel

The phase derivatives come from the original model on (1,2). Outside
the cutoff's closed support the actual kernel is locally zero.
-/

noncomputable section

open Complex Set Filter Expdb
open scoped ContDiff FourierTransform Topology

namespace TaoTrudgianYang2025

theorem norm_modelPhaseBufferedKernel_le_one (l r η T N x : ℝ) (F : ℝ → ℝ) :
    ‖modelPhaseWeightedKernel (modelPhaseBufferedCutoff l r η) F T N x‖ ≤ 1 := by
  simp only [modelPhaseWeightedKernel,norm_mul,Circle.norm_coe,mul_one,
    Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (modelPhaseBufferedCutoff_nonneg _ _ _ _)]
  exact modelPhaseBufferedCutoff_le_one _ _ _ _

theorem modelPhaseBufferedKernel_uniform_second_derivative
    {σ : ℝ} (hσ : 0 ≤ σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l r η : ℝ), 1 ≤ l → r ≤ 2 → 0 < η → η ≤ 1 →
      ∀ (F : ℝ → ℝ) (δ T : ℝ), δ ≤ 1 →
        IsApproximateModelPhaseFunction F σ 1 δ →
        ∀ u : ℝ,
          ‖iteratedDeriv 2 (modelPhaseWeightedKernel
            (modelPhaseBufferedCutoff l r η) F T 1) u‖ ≤ C*(η⁻¹)^2*(1+|T|)^2 := by
  obtain ⟨M,hM,hcut⟩ := modelPhaseBufferedCutoff_uniform_c2
  let K := 1+modelPhaseJetCoefficient σ 0+modelPhaseJetCoefficient σ 1
  let D := (2*Real.pi)^2*K^2+2*Real.pi*K+1
  have hK : 1 ≤ K := by
    dsimp [K]
    linarith [modelPhaseJetCoefficient_nonneg σ 0,modelPhaseJetCoefficient_nonneg σ 1]
  have hD : 1 ≤ D := by
    have hK₀ : 0 ≤ K := by linarith
    dsimp [D]
    have hh : 0 ≤ (2*Real.pi)^2*K^2+2*Real.pi*K := by positivity
    linarith
  refine ⟨4*M*D,by nlinarith [mul_le_mul hM hD (by norm_num) (by linarith : 0 ≤ M)],?_⟩
  intro l r η hl hr hη hη₁ F δ T hδ hF u
  let χ := modelPhaseBufferedCutoff l r η
  have heq : modelPhaseWeightedKernel χ F T 1 =
      fun x => (χ x : ℂ)*(𝐞 (T*F x) : ℂ) := by
    funext x
    simp only [modelPhaseWeightedKernel,div_one]
  by_cases hu : u ∈ tsupport χ
  · have hu' : u ∈ Ioo (1 : ℝ) 2 :=
      modelPhaseBufferedCutoff_tsupport_model hη hl hr hu
    have hphase := intervalC2Bound_fourierChar_of_derivative_bounds (a := u) (b := u) hK
      (F := F) (fun x hx => by
        have hx' : x = u := le_antisymm hx.2 hx.1
        subst x
        exact (approximateModelPhase_contDiffAt hF hu').of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      (fun x hx => by
        have hx' : x = u := le_antisymm hx.2 hx.1
        subst x
        have hb := approximateModelPhase_iteratedDeriv_abs_le hσ hF hu' 0 (by norm_num)
        simp only [zero_add,iteratedDeriv_one] at hb
        dsimp [K]
        linarith [modelPhaseJetCoefficient_nonneg σ 1])
      (fun x hx => by
        have hx' : x = u := le_antisymm hx.2 hx.1
        subst x
        have hb := approximateModelPhase_iteratedDeriv_abs_le hσ hF hu' 1 le_rfl
        dsimp [K]
        linarith [modelPhaseJetCoefficient_nonneg σ 0]) T
    have hA : 1 ≤ η⁻¹ := (one_le_inv₀ hη).mpr hη₁
    have hR₁ : η⁻¹ ≤ η⁻¹*(1+|T|) :=
      le_mul_of_one_le_right (by positivity) (by linarith [abs_nonneg T])
    have hR₂ : 1+|T| ≤ η⁻¹*(1+|T|) :=
      le_mul_of_one_le_left (by positivity) hA
    have hp := ((hcut l r η u u hη).mono le_rfl hR₁).mul
      (hphase.mono le_rfl hR₂)
    rw [heq]
    convert hp.second_le u ⟨le_rfl,le_rfl⟩ using 1
    dsimp [χ,D]
    ring
  · have hz : modelPhaseWeightedKernel χ F T 1 =ᶠ[𝓝 u] fun _ => (0 : ℂ) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hu] with x hx
      simp only [modelPhaseWeightedKernel,div_one,hx,Pi.zero_apply,Complex.ofReal_zero,zero_mul]
    rw [hz.iteratedDeriv_eq 2]
    simp only [iteratedDeriv_const,show (2 : ℕ) ≠ 0 by norm_num,if_false,norm_zero]
    have hM₀ : 0 ≤ M := by linarith
    have hD₀ : 0 ≤ D := by linarith
    positivity

end TaoTrudgianYang2025
