import Dubon2026.AdelicSmoothOrbitJets
import Dubon2026.AdelicOrbitJetIdentification
import Dubon2026.AdelicRaisingLieModule

/-! # The original holomorphic Hilbert slice belongs to the original raising closure -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ContDiff

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

private theorem closedSubmodule_sum_image_mem {V W : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (T : V →L[ℂ] W) (p : Submodule ℂ W) (hp : IsClosed (p : Set W))
    (q : ℕ → V) (hs : Summable q) (hq : ∀ n, T (q n) ∈ p) : T (∑' n, q n) ∈ p := by
  apply hp.mem_of_tendsto (T.hasSum hs.hasSum).tendsto_sum_nat
  exact Filter.Eventually.of_forall (fun n => p.sum_mem (fun i _ => hq i))

/-- The original measurable unipotent jet equals the actual derivative of the original L2 orbit. -/
theorem adelicUnipotentL2Jet_eq_iteratedDeriv (n : ℕ) (t : ℝ) :
    adelicUnipotentL2Jet N f n t = iteratedDeriv n (fun u : ℝ => adelicProjectiveCyclicToL2 N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation
        (adelicRealSL2Embedding (realUpperUnipotent u)) (adelicCyclicGenerator N f))) t := by
  apply Lp.ext
  exact (adelicUnipotentPointwiseJet_memLp N f n t).coeFn_toLp.trans
    (adelicCyclicGenerator_unipotent_L2_jets_ae N f n t).symm

/-- The actual Hilbert retraction of every original L2 jet is its original Hilbert orbit derivative. -/
theorem adelicUnipotentL2Jet_retraction (n : ℕ) (t : ℝ) :
    adelicCyclicHilbertL2Retraction f (adelicUnipotentL2Jet N f n t) =
      iteratedDeriv n (fun u : ℝ => adelicCyclicHilbertRepresentation f
        (adelicRealSL2Embedding (realUpperUnipotent u)) (adelicCyclicHilbertGenerator f)) t := by
  let C : ℝ → AdelicCyclicHilbert f := fun u => adelicCyclicHilbertRepresentation f
    (adelicRealSL2Embedding (realUpperUnipotent u)) (adelicCyclicHilbertGenerator f)
  have hd := congrFun (@iteratedDeriv_continuousLinearMap (AdelicCyclicHilbert f)
    (Lp ℂ 2 (adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)))
    inferInstance inferInstance inferInstance inferInstance
    ((adelicCyclicHilbertToL2 f).restrictScalars ℝ) C
    (adelicCyclicHilbertGenerator_unipotent_contDiff f) n) t
  have he : (fun u => adelicCyclicHilbertToL2 f (C u)) =
      (fun u : ℝ => adelicProjectiveCyclicToL2 N f
        ((adelicLiftCyclicRepresentation N k f).toRepresentation
          (adelicRealSL2Embedding (realUpperUnipotent u)) (adelicCyclicGenerator N f))) :=
    funext (fun u => adelicCyclicHilbertGenerator_orbit_toL2 f
      (adelicRealSL2Embedding (realUpperUnipotent u)))
  change iteratedDeriv n (fun u => adelicCyclicHilbertToL2 f (C u)) t =
    adelicCyclicHilbertToL2 f (iteratedDeriv n C t) at hd
  rw [he] at hd
  exact (congrArg (adelicCyclicHilbertL2Retraction f)
    ((adelicUnipotentL2Jet_eq_iteratedDeriv f n t).trans hd)).trans
      (adelicCyclicHilbertL2Retraction_toL2 f (iteratedDeriv n C t))

/-- Original smooth raising-span vectors retain membership in the original Hilbert closure. -/
theorem adelicRaisingSpan_val_mem_closedSpan (v : adelicRealSmoothSubmodule f)
    (hv : v ∈ adelicRaisingSpan f) : v.val ∈ adelicRaisingClosedSpan f := by
  induction hv using Submodule.span_induction with
  | mem x hx => obtain ⟨n, rfl⟩ := hx; exact adelicRaisingJet_mem_closedSpan f n
  | zero => exact (adelicRaisingClosedSpan f).zero_mem
  | add x y hx hy ihx ihy => exact (adelicRaisingClosedSpan f).add_mem ihx ihy
  | smul c x hx ih => exact (adelicRaisingClosedSpan f).smul_mem c ih

/-- Every literal original unipotent infinitesimal power of the cusp generator lies in the genuine raising span. -/
theorem adelicSmoothGenerator_unipotent_power_mem (hf : f ≠ 0) (n : ℕ) :
    ((adelicSmoothInfinitesimal f realUpperUnipotent realUpperUnipotent_entries_contDiff) ^ n)
      (adelicSmoothGenerator f) ∈ adelicRaisingSpan f := by
  induction n with
  | zero => exact adelicSmoothGenerator_mem_raisingSpan f
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply]
      have h := adelicRaisingSpan_lie f hf complexSl2U _ ih
      change adelicComplexSl2Action f complexSl2U _ ∈ adelicRaisingSpan f at h
      exact (congrArg (fun T : Module.End ℂ (adelicRealSmoothSubmodule f) =>
        T (((adelicSmoothInfinitesimal f realUpperUnipotent
          realUpperUnipotent_entries_contDiff) ^ n) (adelicSmoothGenerator f)))
            (adelicComplexSl2Action_U f)) ▸ h

/-- The original retracted Taylor coefficient is exactly the corresponding original infinitesimal power divided by its factorial. -/
theorem adelicUnipotentTaylorCoefficient_retraction (n : ℕ) :
    adelicCyclicHilbertL2Retraction f (adelicUnipotentTaylorCoefficient N f n) =
      (n.factorial : ℂ)⁻¹ •
        (((adelicSmoothInfinitesimal f realUpperUnipotent realUpperUnipotent_entries_contDiff) ^ n)
          (adelicSmoothGenerator f)).val := by
  have he := (adelicUnipotentL2Jet_retraction f n 0).trans
    (adelicSmoothInfinitesimal_iteratedDeriv_zero f realUpperUnipotent
      realUpperUnipotent_entries_contDiff realUpperUnipotent_add realUpperUnipotent_zero
      (adelicSmoothGenerator f) n)
  exact ((adelicCyclicHilbertL2Retraction f).map_smul (n.factorial : ℂ)⁻¹
    (adelicUnipotentL2Jet N f n 0)).trans
      (congrArg (fun v : AdelicCyclicHilbert f => (n.factorial : ℂ)⁻¹ • v) he)

/-- Every genuine retracted holomorphic coefficient lies in the original closed raising span. -/
theorem adelicUnipotentTaylorCoefficient_mem_closedSpan (hf : f ≠ 0) (n : ℕ) :
    adelicCyclicHilbertL2Retraction f (adelicUnipotentTaylorCoefficient N f n) ∈
      adelicRaisingClosedSpan f := by
  rw [adelicUnipotentTaylorCoefficient_retraction]
  exact (adelicRaisingClosedSpan f).smul_mem _ (adelicRaisingSpan_val_mem_closedSpan f _
    (adelicSmoothGenerator_unipotent_power_mem f hf n))

/-- The genuine local holomorphic Hilbert slice lies in the closure of the original raising derivatives. -/
theorem adelicHolomorphicL2Curve_retraction_mem_closedSpan (hf : f ≠ 0)
    {z : ℂ} (hz : ‖z‖ < (1 / 2 : ℝ)) :
    adelicCyclicHilbertL2Retraction f (adelicHolomorphicL2Curve N f z) ∈
      adelicRaisingClosedSpan f := by
  obtain ⟨K, _, hK⟩ := adelicUnipotentTaylorCoefficient_norm_bound N f
  apply @closedSubmodule_sum_image_mem
    (Lp ℂ 2 (adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)))
    (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance inferInstance
    (adelicCyclicHilbertL2Retraction f) (adelicRaisingClosedSpan f)
    (Submodule.isClosed_topologicalClosure _) _
    (vectorPowerSeries_summable (adelicUnipotentTaylorCoefficient N f) hK hz)
  intro n
  exact ((adelicCyclicHilbertL2Retraction f).map_smul (z ^ n)
    (adelicUnipotentTaylorCoefficient N f n)).symm ▸
      (adelicRaisingClosedSpan f).smul_mem _ (adelicUnipotentTaylorCoefficient_mem_closedSpan f hf n)

/-- Every original affine generator orbit in the proved holomorphic neighborhood lies in its original raising closure. -/
theorem adelicCyclicHilbertGenerator_affine_mem_closedSpan (hf : f ≠ 0) (x y : ℝ)
    (hz : ‖realAffineHolomorphicParameter x y‖ < (1 / 2 : ℝ)) :
    adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (realAffineMatrix x (Real.exp_pos y)))
      (adelicCyclicHilbertGenerator f) ∈ adelicRaisingClosedSpan f := by
  exact (adelicCyclicHilbertGenerator_affine_formula f x y hz).symm ▸
    (adelicRaisingClosedSpan f).smul_mem _
      (adelicHolomorphicL2Curve_retraction_mem_closedSpan f hf hz)

end
end Dubon2026
