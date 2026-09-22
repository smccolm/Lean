import TaoTrudgianYang2025.BetaSecondDerivative
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Physical discrete curvature of actual model phases

The radians conversion and the original N,T scales are explicit.
Only strictly interior sample points are differentiated; boundary terms
are retained separately in the finite-sum consumer.
-/

noncomputable section

open Set Expdb
open scoped ContDiff
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

def betaModelSample (F : ℝ → ℝ) (T N A x : ℝ) : ℝ :=
  -2*Real.pi*T*F ((A+x)/N)

theorem betaModelSample_hasDerivAt {F : ℝ → ℝ} {T N A x : ℝ}
    (hF : ContDiffOn ℝ ∞ F phaseInterval) (hu : (A+x)/N ∈ Ioo (1 : ℝ) 2) :
    HasDerivAt (betaModelSample F T N A)
      ((-2*Real.pi*T/N)*deriv F ((A+x)/N)) x := by
  have hc : ContDiffAt ℝ 1 F ((A+x)/N) :=
    (hF.contDiffAt (Icc_mem_nhds hu.1 hu.2)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)
  have hin : HasDerivAt (fun y : ℝ => (A+y)/N) (1/N) x :=
    ((hasDerivAt_id x).const_add A).div_const N
  convert ((hc.differentiableAt_one.hasDerivAt.comp x hin).const_mul
    (-2*Real.pi*T)) using 1
  dsimp [betaModelSample]
  ring

theorem betaModelSample_firstDeriv_hasDerivAt {F : ℝ → ℝ} {T N A x : ℝ}
    (hF : ContDiffOn ℝ ∞ F phaseInterval) (hu : (A+x)/N ∈ Ioo (1 : ℝ) 2) :
    HasDerivAt (fun y : ℝ => (-2*Real.pi*T/N)*deriv F ((A+y)/N))
      ((-2*Real.pi*T/N^2)*deriv (deriv F) ((A+x)/N)) x := by
  have hc : ContDiffAt ℝ 2 F ((A+x)/N) :=
    (hF.contDiffAt (Icc_mem_nhds hu.1 hu.2)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hd : ContDiffAt ℝ 1 (deriv F) ((A+x)/N) :=
    hc.derivWithin (by norm_num)
  have hin : HasDerivAt (fun y : ℝ => (A+y)/N) (1/N) x :=
    ((hasDerivAt_id x).const_add A).div_const N
  convert ((hd.differentiableAt_one.hasDerivAt.comp x hin).const_mul
    (-2*Real.pi*T/N)) using 1
  ring

theorem betaModelSample_secondDifference_bounds
    {σ δ T N A : ℝ} {F : ℝ → ℝ} {L : ℕ}
    (hσ : 0 < σ) (hT : 0 < T) (hN : 0 < N)
    (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hstart : N < A) (hend : A+(L : ℝ)+1 < 2*N)
    (n : ℕ) (hn : n < L) :
    (2*Real.pi*modelPhaseCurvatureLower σ)*T/N^2 ≤
      (betaModelSample F T N A (n+2)-betaModelSample F T N A (n+1)) -
        (betaModelSample F T N A (n+1)-betaModelSample F T N A n) ∧
    (betaModelSample F T N A (n+2)-betaModelSample F T N A (n+1)) -
        (betaModelSample F T N A (n+1)-betaModelSample F T N A n) ≤
      (2*Real.pi*(σ+1))*T/N^2 := by
  have hinside (x : ℝ) (hx : x ∈ Icc (n : ℝ) (n+2)) :
      (A+x)/N ∈ Ioo (1 : ℝ) 2 := by
    have hn' : (n : ℝ)+1 ≤ L := by exact_mod_cast hn
    constructor
    · apply (lt_div_iff₀ hN).2
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n),hx.1]
    · apply (div_lt_iff₀ hN).2
      linarith [hx.2]
  obtain ⟨x,hx,heq⟩ := second_order_mean_value
    (betaModelSample F T N A)
    (fun y => (-2*Real.pi*T/N)*deriv F ((A+y)/N))
    (fun y => (-2*Real.pi*T/N^2)*deriv (deriv F) ((A+y)/N))
    n
    (fun y hy => betaModelSample_hasDerivAt hF.1 (hinside y hy))
    (fun y hy => betaModelSample_firstDeriv_hasDerivAt hF.1 (hinside y hy))
  have hc := approximateModelPhase_curvature_deriv_bounds hσ hδ hF
    (hinside x ⟨hx.1.le,hx.2.le⟩)
  have hfactor : 0 ≤ 2*Real.pi*T/N^2 := by positivity
  have hlower := mul_le_mul_of_nonneg_left hc.1 hfactor
  have hupper := mul_le_mul_of_nonneg_left hc.2 hfactor
  ring_nf at heq hlower hupper ⊢
  constructor <;> linarith

end TaoTrudgianYang2025
