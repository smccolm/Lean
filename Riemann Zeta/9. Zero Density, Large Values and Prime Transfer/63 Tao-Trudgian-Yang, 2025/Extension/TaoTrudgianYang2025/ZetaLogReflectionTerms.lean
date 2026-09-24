import TaoTrudgianYang2025.ZetaLogStationaryData
import TaoTrudgianYang2025.BetaBufferedRetainedGeometry
import TaoTrudgianYang2025.BetaBufferedPowerError

/-!
# Literal logarithmic reflection terms on the true dual annulus

The common phase has norm one. Each retained term is the actual
reciprocal-weighted Dirichlet term, at the original ordinate 2*pi*T.
-/

noncomputable section
open Set Expdb Complex
open scoped FourierTransform BigOperators
namespace TaoTrudgianYang2025

def zetaLogReflectionCarrier (T N : ℝ) : ℂ :=
  𝐞 (T*Real.log (T/N)-T-1/8)

theorem norm_zetaLogReflectionCarrier (T N : ℝ) :
    ‖zetaLogReflectionCarrier T N‖ = 1 := Circle.norm_coe _

theorem modelPhaseStationaryCharacter_log {T N r : ℝ}
    (hT : 0 < T) (hN : 0 < N)
    (hv : r*N/T ∈ modelPhaseSlopeRange Real.log) :
    modelPhaseStationaryCharacter Real.log T N r =
      zetaLogReflectionCarrier T N*(r : ℂ)^(-(I*((2*Real.pi*T : ℝ) : ℂ))) := by
  have hr := logarithmicStationaryFrequency_pos hT hN hv
  rw [modelPhaseStationaryCharacter,modelPhaseFrequencyPhase_log_stationary hT hN hv,
    zetaLogReflectionCarrier,Real.fourierChar_apply,Real.fourierChar_apply,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'),
    ← Complex.ofReal_log hr.le,← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem modelPhaseStationaryMainTerm_log {T N r : ℝ}
    (hT : 0 < T) (hN : 0 < N)
    (hv : r*N/T ∈ modelPhaseSlopeRange Real.log) :
    modelPhaseStationaryMainTerm Real.log T N r =
      zetaLogReflectionCarrier T N*(Real.sqrt T : ℂ)*
        ((r : ℂ)⁻¹*(r : ℂ)^(-(I*((2*Real.pi*T : ℝ) : ℂ)))) := by
  rw [modelPhaseStationaryMainTerm,modelPhasePhysicalAmplitude_log hT hN hv,
    modelPhaseStationaryCharacter_log hT hN hv]
  push_cast
  ring

theorem logarithmicStationaryFrequency_window {T N r : ℝ}
    (hT : 0 < T) (hN : 0 < N)
    (hv : r*N/T ∈ modelPhaseSlopeRange Real.log) :
    T/(2*N) < r ∧ r < T/N := by
  have hpos := modelPhaseSlopeRange_log_pos hv
  have hu := modelPhaseInverseSlope_mem hv
  rw [modelPhaseInverseSlope_log hv] at hu
  have hlo := mul_lt_mul_of_pos_right hu.1 hpos
  have hhi := mul_lt_mul_of_pos_right hu.2 hpos
  rw [inv_mul_cancel₀ hpos.ne'] at hlo hhi
  simp only [one_mul] at hlo
  constructor
  · apply (div_lt_iff₀ (by positivity : 0 < 2*N)).mpr
    have hh := (lt_div_iff₀ hT).mp (show (1/2 : ℝ) < r*N/T by linarith)
    nlinarith
  · apply (lt_div_iff₀ hN).mpr
    exact (div_lt_one hT).mp hlo

theorem logarithmicSharpStationarySet_slope {T N : ℝ} {a b : ℕ} {q : ℤ}
    (hT : 0 < T) (hN : 0 < N) (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N)
    (hq : q ∈ modelPhaseSharpStationarySet Real.log T N a b) :
    (q : ℝ)*N/T ∈ modelPhaseSlopeRange Real.log := by
  apply (modelPhaseSharpStationarySet_critical_geometry
    (by norm_num : (0 : ℝ) < 1)
    (le_min (modelPhaseCurvatureLower_pos (by norm_num : (0 : ℝ) < 1)).le (by norm_num))
    (log_approximateModel 1 (le_refl 0)) hT hN ha hb hq).1

theorem logarithmicSharpStationarySet_window {T N : ℝ} {a b : ℕ} {q : ℤ}
    (hT : 0 < T) (hN : 0 < N) (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N)
    (hq : q ∈ modelPhaseSharpStationarySet Real.log T N a b) :
    T/(2*N) < (q : ℝ) ∧ (q : ℝ) < T/N :=
  logarithmicStationaryFrequency_window hT hN
    (logarithmicSharpStationarySet_slope hT hN ha hb hq)

theorem norm_logarithmicSharpStationarySum {T N : ℝ} {a b : ℕ}
    (hT : 0 < T) (hN : 0 < N) (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N) :
    ‖∑ q ∈ modelPhaseSharpStationarySet Real.log T N a b,
        modelPhaseStationaryMainTerm Real.log T N q‖ =
      Real.sqrt T*‖∑ q ∈ modelPhaseSharpStationarySet Real.log T N a b,
        (q : ℂ)⁻¹*(q : ℂ)^(-(I*((2*Real.pi*T : ℝ) : ℂ)))‖ := by
  have hsum :
      (∑ q ∈ modelPhaseSharpStationarySet Real.log T N a b,
        modelPhaseStationaryMainTerm Real.log T N q) =
      zetaLogReflectionCarrier T N*(Real.sqrt T : ℂ)*
        ∑ q ∈ modelPhaseSharpStationarySet Real.log T N a b,
          (q : ℂ)⁻¹*(q : ℂ)^(-(I*((2*Real.pi*T : ℝ) : ℂ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    simpa only [Complex.ofReal_intCast] using
      modelPhaseStationaryMainTerm_log hT hN
        (logarithmicSharpStationarySet_slope hT hN ha hb hq)
  rw [hsum,norm_mul,norm_mul,norm_zetaLogReflectionCarrier,one_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg T)]

end TaoTrudgianYang2025
