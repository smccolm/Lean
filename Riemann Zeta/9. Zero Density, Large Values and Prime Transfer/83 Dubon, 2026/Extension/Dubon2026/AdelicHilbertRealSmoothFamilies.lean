import Dubon2026.RealGroupSmoothCoordinates

/-! # Hilbert smoothness of the original generator along every smooth real matrix family -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup MeasureTheory Filter
open scoped MatrixGroups ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every smooth actual real matrix family whose original Möbius coordinate lies in the proved disk gives a smooth original Hilbert orbit. -/
theorem adelicCyclicHilbertGenerator_real_contDiffAt_of_disk {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (h : E → SL(2, ℝ)) {x : E}
    (hh : ∀ i j : Fin 2, ContDiffAt ℝ ∞ (fun w => h w i j) x)
    (hz : ‖realGroupHolomorphicParameter (h x)‖ < (1 / 2 : ℝ)) :
    ContDiffAt ℝ ∞ (fun w => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (h w)) (adelicCyclicHilbertGenerator f)) x := by
  letI : IsScalarTower ℝ ℂ (AdelicCyclicHilbert f) := inferInstance
  have hZ := realGroupHolomorphicParameter_contDiffAt h hh
  have hH := (adelicHolomorphicL2Curve_contDiffAt N f hz).comp x hZ
  have hr := @ContinuousLinearMap.contDiff ℝ
    (Lp ℂ 2 (adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)))
    (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance inferInstance inferInstance ∞
    ((adelicCyclicHilbertL2Retraction f).restrictScalars ℝ)
  have hR := hr.contDiffAt.comp x hH
  have ht := (realGroupWeight_contDiffAt k h hh).smul hR
  apply ht.congr_of_eventuallyEq
  have hnb : ∀ᶠ w in 𝓝 x, ‖realGroupHolomorphicParameter (h w)‖ < (1 / 2 : ℝ) :=
    hZ.continuousAt.norm.tendsto.eventually (isOpen_Iio.mem_nhds hz)
  filter_upwards [hnb] with w hw
  exact adelicCyclicHilbertGenerator_real_formula f (h w) hw

/-- The original completed generator is smooth along every smooth family of actual real determinant-one matrices, at every parameter. -/
theorem adelicCyclicHilbertGenerator_real_contDiffAt {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (h : E → SL(2, ℝ)) {x : E}
    (hh : ∀ i j : Fin 2, ContDiffAt ℝ ∞ (fun w => h w i j) x) :
    ContDiffAt ℝ ∞ (fun w => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (h w)) (adelicCyclicHilbertGenerator f)) x := by
  let c : E → SL(2, ℝ) := fun w => (h x)⁻¹ * h w
  have hc : ∀ i j : Fin 2, ContDiffAt ℝ ∞ (fun w => c w i j) x :=
    realSL2_left_mul_entries_contDiffAt (h x)⁻¹ h hh
  have hz : ‖realGroupHolomorphicParameter (c x)‖ < (1 / 2 : ℝ) := by
    norm_num [c, realGroupHolomorphicParameter]
  have hC := adelicCyclicHilbertGenerator_real_contDiffAt_of_disk f c hc hz
  have hL := @ContinuousLinearMap.contDiff ℝ (AdelicCyclicHilbert f)
    (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance inferInstance inferInstance ∞
    ((adelicCyclicHilbertOperator f (adelicRealSL2Embedding (h x))).restrictScalars ℝ)
  have ht := hL.contDiffAt.comp x hC
  change ContDiffAt ℝ ∞ (fun w => adelicCyclicHilbertRepresentation f
    (adelicRealSL2Embedding (h x)) (adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (c w)) (adelicCyclicHilbertGenerator f))) x at ht
  apply ht.congr_of_eventuallyEq
  apply Eventually.of_forall
  intro w
  dsimp only
  rw [← Module.End.mul_apply, ← map_mul, ← map_mul]
  simp only [c, mul_inv_cancel_left]

/-- Entrywise smoothness of an actual real matrix family yields global Hilbert smoothness of the original completed generator orbit. -/
theorem adelicCyclicHilbertGenerator_real_contDiff {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (h : E → SL(2, ℝ))
    (hh : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun w => h w i j)) :
    ContDiff ℝ ∞ (fun w => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (h w)) (adelicCyclicHilbertGenerator f)) := by
  exact contDiff_iff_contDiffAt.mpr (fun _ =>
    adelicCyclicHilbertGenerator_real_contDiffAt f h (fun i j => (hh i j).contDiffAt))

end
end Dubon2026
