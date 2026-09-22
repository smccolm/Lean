import TaoTrudgianYang2025.BetaInverseStability

/-!
# Physical stationary points for the model-phase B transformation

The frequency r is linked to the original positive N,T scales by v=r*N/T.
The unique critical point, its dual-phase value and its second derivative
are derived for the actual phase T*F(x/N)-r*x. No stationary-phase integral
or Poisson summation formula is asserted here.
-/

noncomputable section

open Set Expdb Filter
open scoped Topology ContDiff FourierTransform

namespace TaoTrudgianYang2025

def modelPhaseFrequencyPhase (F : ℝ → ℝ) (T N r x : ℝ) : ℝ :=
  T * F (x/N) - r*x

def modelPhaseStationaryPoint (F : ℝ → ℝ) (T N r : ℝ) : ℝ :=
  N * modelPhaseInverseSlope F (r*N/T)

theorem modelPhaseStationaryPoint_mem {F : ℝ → ℝ} {T N r : ℝ}
    (hN : 0 < N) (hv : r*N/T ∈ modelPhaseSlopeRange F) :
    modelPhaseStationaryPoint F T N r ∈ Ioo N (2*N) := by
  rcases modelPhaseInverseSlope_mem hv with ⟨hu₁, hu₂⟩
  unfold modelPhaseStationaryPoint
  constructor <;> nlinarith

theorem modelPhaseStationaryPoint_div {F : ℝ → ℝ} {T N r : ℝ}
    (hN : N ≠ 0) :
    modelPhaseStationaryPoint F T N r / N = modelPhaseInverseSlope F (r*N/T) := by
  unfold modelPhaseStationaryPoint
  field_simp

theorem modelPhaseFrequencyPhase_hasDerivAt
    {σ δ T N r x : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hx : x/N ∈ Ioo (1 : ℝ) 2) :
    HasDerivAt (modelPhaseFrequencyPhase F T N r) (T/N*deriv F (x/N)-r) x := by
  have hd := (approximateModelPhase_contDiffAt hF hx).differentiableAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  convert ((hd.hasDerivAt.comp x ((hasDerivAt_id x).div_const N)).const_mul T).sub
    ((hasDerivAt_id x).const_mul r) using 1
  ring

theorem modelPhaseStationaryPoint_hasDerivAt
    {σ δ T N r : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hT : T ≠ 0) (hN : N ≠ 0)
    (hv : r*N/T ∈ modelPhaseSlopeRange F) :
    HasDerivAt (modelPhaseFrequencyPhase F T N r) 0
      (modelPhaseStationaryPoint F T N r) := by
  have hx : modelPhaseStationaryPoint F T N r / N ∈ Ioo (1 : ℝ) 2 := by
    rw [modelPhaseStationaryPoint_div hN]
    exact modelPhaseInverseSlope_mem hv
  have hd := modelPhaseFrequencyPhase_hasDerivAt hF hx (r := r) (T := T)
  rw [modelPhaseStationaryPoint_div hN, deriv_modelPhaseInverseSlope_apply hv] at hd
  convert hd using 1
  field_simp
  ring

theorem modelPhaseStationaryPoint_unique
    {σ δ T N r x : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : T ≠ 0) (hN : 0 < N)
    (hx : x ∈ Ioo N (2*N))
    (hcrit : deriv (modelPhaseFrequencyPhase F T N r) x = 0) :
    x = modelPhaseStationaryPoint F T N r := by
  have hu : x/N ∈ Ioo (1 : ℝ) 2 := by
    constructor
    · exact (lt_div_iff₀ hN).2 (by simpa using hx.1)
    · exact (div_lt_iff₀ hN).2 hx.2
  rw [(modelPhaseFrequencyPhase_hasDerivAt hF hu).deriv] at hcrit
  have he : deriv F (x/N) = r*N/T := by
    field_simp at hcrit ⊢
    nlinarith
  have hi := modelPhaseInverseSlope_deriv hσ hδ hF hu
  rw [he] at hi
  unfold modelPhaseStationaryPoint
  rw [hi]
  field_simp

theorem modelPhaseStationaryPoint_phase
    {F : ℝ → ℝ} {T N r : ℝ} (hT : T ≠ 0) (hN : N ≠ 0) :
    modelPhaseFrequencyPhase F T N r (modelPhaseStationaryPoint F T N r) =
      -T * modelPhaseLegendreDual F (r*N/T) := by
  unfold modelPhaseFrequencyPhase
  rw [modelPhaseStationaryPoint_div hN]
  unfold modelPhaseStationaryPoint modelPhaseLegendreDual
  field_simp
  ring

theorem modelPhaseFrequencyPhase_secondDeriv
    {σ δ T N r x : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hx : x/N ∈ Ioo (1 : ℝ) 2) :
    deriv (deriv (modelPhaseFrequencyPhase F T N r)) x =
      T/N^2 * deriv (deriv F) (x/N) := by
  have hd := (approximateModelPhase_deriv_contDiffAt hF hx).differentiableAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hh := ((hd.hasDerivAt.comp x ((hasDerivAt_id x).div_const N)).const_mul
    (T/N)).sub_const r
  have heq : deriv (modelPhaseFrequencyPhase F T N r) =ᶠ[𝓝 x]
      (fun y => T/N * deriv F (y/N) - r) := by
    have hc : ContinuousAt (fun y : ℝ => y/N) x := continuousAt_id.div_const N
    filter_upwards [hc (isOpen_Ioo.mem_nhds hx)] with y hy
    exact (modelPhaseFrequencyPhase_hasDerivAt hF hy).deriv
  simp only [Function.comp_apply, id_eq] at hh
  rw [heq.deriv_eq, hh.deriv]
  ring

theorem modelPhaseStationaryPoint_curvature
    {σ δ T N r : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N)
    (hv : r*N/T ∈ modelPhaseSlopeRange F) :
    (T/N^2)*modelPhaseCurvatureLower σ ≤
        -deriv (deriv (modelPhaseFrequencyPhase F T N r))
          (modelPhaseStationaryPoint F T N r) ∧
      -deriv (deriv (modelPhaseFrequencyPhase F T N r))
          (modelPhaseStationaryPoint F T N r) ≤ (T/N^2)*(σ+1) := by
  have hx : modelPhaseStationaryPoint F T N r / N ∈ Ioo (1 : ℝ) 2 := by
    rw [modelPhaseStationaryPoint_div hN.ne']
    exact modelPhaseInverseSlope_mem hv
  rw [modelPhaseFrequencyPhase_secondDeriv hF hx]
  have hb := approximateModelPhase_curvature_deriv_bounds hσ hδ hF hx
  have hp : 0 ≤ T/N^2 := by positivity
  constructor
  · have hh := mul_le_mul_of_nonneg_left hb.1 hp
    nlinarith
  · have hh := mul_le_mul_of_nonneg_left hb.2 hp
    nlinarith

theorem modelPhaseStationaryPoint_fourier_sign
    {F : ℝ → ℝ} {T N r : ℝ} (hT : T ≠ 0) (hN : N ≠ 0) :
    𝐞 (modelPhaseFrequencyPhase F T N r (modelPhaseStationaryPoint F T N r)) =
      starRingEnd ℂ (𝐞 (T * modelPhaseLegendreDual F (r*N/T))) := by
  rw [modelPhaseStationaryPoint_phase hT hN]
  simp only [Real.fourierChar_apply, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_mul, Complex.ofReal_neg]
  congr 1
  ring

end TaoTrudgianYang2025
