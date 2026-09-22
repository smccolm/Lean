import TaoTrudgianYang2025.BetaMorseSupport
import TaoTrudgianYang2025.BetaModelJetEstimates

/-!
# Uniform derivatives of actual averaged curvature

Differentiating the fixed segment average inserts powers of t. The
original finite-order model bounds therefore control every requested
averaged-curvature derivative, uniformly in the phase and stationary slope.
-/

noncomputable section

open Set Expdb Filter MeasureTheory
open scoped ContDiff Topology

namespace TaoTrudgianYang2025

theorem iteratedDeriv_segmentTaylorAverage
    {f : ℝ → ℝ} {l r a x : ℝ}
    (hf : ∀ u ∈ Ioo l r, ContDiffAt ℝ ∞ f u)
    (ha : a ∈ Ioo l r) (hx : x ∈ Ioo l r) (k n : ℕ) :
    iteratedDeriv n (segmentTaylorAverage f a k) x =
      segmentTaylorAverage f a (k+n) x := by
  induction n generalizing x with
  | zero => simp only [iteratedDeriv_zero,Nat.add_zero]
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have he : iteratedDeriv n (segmentTaylorAverage f a k) =ᶠ[𝓝 x]
          segmentTaylorAverage f a (k+n) := by
        filter_upwards [isOpen_Ioo.mem_nhds hx] with u hu
        exact ih hu
      rw [he.deriv_eq,(segmentTaylorAverage_hasDerivAt hf ha hx (k+n)).deriv,Nat.add_assoc]

theorem abs_segmentTaylorAverage_le
    {f : ℝ → ℝ} {l r a x M : ℝ}
    (ha : a ∈ Ioo l r) (hx : x ∈ Ioo l r) (k : ℕ)
    (hb : ∀ u ∈ Ioo l r, |iteratedDeriv k f u| ≤ M) :
    |segmentTaylorAverage f a k x| ≤ M := by
  have hpoint : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      ‖(1-t)*t^k*iteratedDeriv k f (a+t*(x-a))‖ ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hf : 0 ≤ (1-t)*t^k := mul_nonneg (by linarith [ht.2]) (pow_nonneg ht.1 k)
    have hf' : (1-t)*t^k ≤ 1 := by
      have hp : t^k ≤ 1 := pow_le_one₀ ht.1 ht.2
      nlinarith [mul_nonneg ht.1 (pow_nonneg ht.1 k)]
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg hf]
    exact (mul_le_of_le_one_left (norm_nonneg _) hf').trans
      (hb _ (affineSegment_mem_Ioo ha hx ht))
  have h := norm_integral_le_of_norm_le_const hpoint
  simpa [segmentTaylorAverage,Real.norm_eq_abs,Measure.real] using h

theorem approximateModelPhase_iteratedDeriv_abs_le
    {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hσ : 0 ≤ σ) (hF : IsApproximateModelPhaseFunction F σ P δ)
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) (p : ℕ) (hp : p ≤ P) :
    |iteratedDeriv (p+1) F u| ≤ modelPhaseJetCoefficient σ p+δ := by
  calc
    _ = |(iteratedDeriv (p+1) F u-iteratedDeriv p (modelPhase σ) u)+
        iteratedDeriv p (modelPhase σ) u| := by congr 1; ring
    _ ≤ |iteratedDeriv (p+1) F u-iteratedDeriv p (modelPhase σ) u|+
        |iteratedDeriv p (modelPhase σ) u| := abs_add_le _ _
    _ ≤ δ+modelPhaseJetCoefficient σ p := add_le_add
      (approximateModelPhase_iteratedDeriv_error hF hu p hp)
      (iteratedDeriv_modelPhase_abs_le hσ hu p)
    _ = _ := by ring

theorem iteratedDeriv_modelPhaseAveragedCurvature
    {F : ℝ → ℝ} {σ δ v u : ℝ} {P : ℕ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2) (k : ℕ) :
    iteratedDeriv k (modelPhaseAveragedCurvature F v) u =
      -2*segmentTaylorAverage (deriv (deriv F)) (modelPhaseInverseSlope F v) k u := by
  have hj : ∀ x ∈ Ioo (1 : ℝ) 2, ContDiffAt ℝ ∞ (deriv (deriv F)) x := by
    intro x hx
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
      approximateModelPhase_iteratedDeriv_contDiffAt hF hx 2
  unfold modelPhaseAveragedCurvature
  rw [iteratedDeriv_const_mul_field,iteratedDeriv_segmentTaylorAverage hj
    (modelPhaseInverseSlope_mem hv) hu,Nat.zero_add]

theorem abs_iteratedDeriv_modelPhaseAveragedCurvature_le
    {F : ℝ → ℝ} {σ δ v u : ℝ} {P : ℕ}
    (hσ : 0 ≤ σ) (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2)
    (k : ℕ) (hk : k+1 ≤ P) :
    |iteratedDeriv k (modelPhaseAveragedCurvature F v) u| ≤
      2*(modelPhaseJetCoefficient σ (k+1)+δ) := by
  rw [iteratedDeriv_modelPhaseAveragedCurvature hF hv hu,abs_mul]
  norm_num only [abs_neg]
  apply mul_le_mul_of_nonneg_left (abs_segmentTaylorAverage_le
    (modelPhaseInverseSlope_mem hv) hu k ?_) (by norm_num : (0 : ℝ) ≤ 2)
  intro x hx
  simpa only [iteratedDeriv_succ'] using
    approximateModelPhase_iteratedDeriv_abs_le hσ hF hx (k+1) hk

end TaoTrudgianYang2025
