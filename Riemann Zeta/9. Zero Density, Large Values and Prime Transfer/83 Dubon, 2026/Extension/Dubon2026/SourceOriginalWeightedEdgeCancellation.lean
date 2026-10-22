import Dubon2026.SourceOriginalWeightedArcReversal

/-! DUB-17/18 -> raw reciprocity -> weighted residue-jump identity.
An actual constant primitive jump and the proved reversal law cancel the two
oriented weighted integrals to the jump times the actual positive edge integral.
The separate dissection consumer constructs the primitive and jump inputs.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set MeasureTheory KaehlerDifferential intervalIntegral
open scoped Interval
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem Cell.weighted_edge_cancellation (C C' : Cell N) (k : Fin C.R.N) (k' : Fin C'.R.N)
    (ψ : ℝ → ℝ) (hanti : StrictAntiOn ψ (C'.R.arcIcc k'))
    (hc : ContDiffOn ℝ 1 ψ (C'.R.arcIcc k'))
    (ha : ψ (C'.R.φs k'.castSucc) = C.R.φs k.succ)
    (hb : ψ (C'.R.φs k'.succ) = C.R.φs k.castSucc)
    (hbd : ∀ t ∈ C'.R.arcIcc k', C'.bdry t = C.bdry (ψ t))
    (θ : Ω[F⁄ℂ]) (hθ : ∀ s ∈ C.R.arcIcc k, 0 ≤ (C.bdry s).ordDifferential θ)
    (Ψ Ψ' : ℂ → ℂ) (hΨ : ∀ w ∈ C.R.K, ContinuousAt Ψ w)
    (hΨ' : ∀ w ∈ C'.R.K, ContinuousAt Ψ' w) (J : ℂ)
    (hJ : ∀ s ∈ C.R.arcIcc k, Ψ (C.R.loop s) - Ψ' (C'.ζ (C.bdry s)) = J) :
    (∫ s in (C.R.φs k.castSucc)..(C.R.φs k.succ), Ψ (C.R.loop s) * C.bdryIntegrand θ s) +
      (∫ t in (C'.R.φs k'.castSucc)..(C'.R.φs k'.succ), Ψ' (C'.R.loop t) * C'.bdryIntegrand θ t) =
        J * ∫ s in (C.R.φs k.castSucc)..(C.R.φs k.succ), C.bdryIntegrand θ s := by
  have hab : C.R.φs k.castSucc < C.R.φs k.succ := C.R.hmono Fin.castSucc_lt_succ
  have hover := C.reversed_arc_overlap C' k k' ψ hc.continuousOn ha hb hbd
  have hP : ContinuousOn (fun s => Ψ (C.R.loop s)) (C.R.arcIcc k) := by
    intro s _
    exact ((hΨ _ (C.R.loop_mem_K s)).comp C.R.continuous_loop.continuousAt).continuousWithinAt
  have hW : ContinuousOn (fun s => Ψ' (C'.ζ (C.bdry s))) (C.R.arcIcc k) := by
    intro s hs
    exact (((hΨ' _ (hover s hs).2).comp (C'.ζ.continuousAt (hover s hs).1)).comp
      C.continuous_bdry.continuousAt).continuousWithinAt
  have hI1 := (C.weighted_arc_integral_extension k θ hθ _ hP).1
  have hI2 := (C.weighted_arc_integral_extension k θ hθ _ hW).1
  rw [C.weighted_reversed_arc_integral C' k k' ψ hanti hc ha hb hbd θ hθ Ψ' hΨ',
    ← sub_eq_add_neg, ← integral_sub hI1 hI2, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le hab.le]
  intro s hs
  dsimp only
  rw [← sub_mul, hJ s hs]

end
end Dubon2026.SourceFunctionField.CellGeometry
