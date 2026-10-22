import Dubon2026.SourceOriginalCellCoefficientTransition
import Dubon2026.SourceOriginalCellBoundaryIntegrability
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! DUB-17/18 -> raw reciprocity -> constant primitive jumps on shared edges.
The actual coefficient transition makes the derivative of two cell primitives'
difference zero along a shared arc. The native fundamental theorem, restricted
to each initial subinterval, extends this equality through both arc endpoints.
The overlap data below are supplied by the source reversed-edge reparameterization.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set MeasureTheory KaehlerDifferential
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem Cell.primitive_jump_on_arc (C C' : Cell N) (k : Fin C.R.N)
    (hover : ∀ s ∈ C.R.arcIcc k,
      C.bdry s ∈ C'.ζ.source ∧ C'.ζ (C.bdry s) ∈ C'.R.K)
    (η : Ω[F⁄ℂ]) (Ψ Ψ' : ℂ → ℂ)
    (hΨ : ∀ w ∈ C.R.K, HasDerivAt Ψ (coeffIn C.ζ η w) w)
    (hΨ' : ∀ w ∈ C'.R.K, HasDerivAt Ψ' (coeffIn C'.ζ η w) w) :
    ∃ J : ℂ, ∀ s ∈ C.R.arcIcc k,
      Ψ (C.R.loop s) - Ψ' (C'.ζ (C.bdry s)) = J := by
  let a := C.R.φs k.castSucc
  let b := C.R.φs k.succ
  let D : ℝ → ℂ := fun s => Ψ (C.R.loop s) - Ψ' (C'.ζ (C.bdry s))
  have hDc : ContinuousOn D (Icc a b) := by
    intro s hs
    have h1 := (hΨ _ (C.R.loop_mem_K s)).continuousAt.comp C.R.continuous_loop.continuousAt
    have h2 := ((hΨ' _ (hover s hs).2).continuousAt.comp
      (C'.ζ.continuousAt (hover s hs).1)).comp C.continuous_bdry.continuousAt
    exact (h1.sub h2).continuousWithinAt
  have hDd : ∀ s ∈ Ioo a b, HasDerivAt D 0 s := by
    intro s hs
    have hsI : s ∈ C.R.arcIcc k := ⟨hs.1.le, hs.2.le⟩
    have hsrc := (C.bdry_coordinates s).1
    have hval := (C.bdry_coordinates s).2
    have hsrc' := (hover s hsI).1
    have hγ := C.R.hasDerivAt_loop k hs
    have h1 := (hΨ _ (C.R.loop_mem_K s)).comp s hγ
    have hTa := C.toAnalyticCoord.analyticAt_transition C'.toAnalyticCoord hsrc hsrc'
    have hTd : HasDerivAt (C'.ζ ∘ C.ζ.symm)
        (deriv (C'.ζ ∘ C.ζ.symm) (C.ζ (C.bdry s))) (C.R.loop s) := by
      rw [← hval]
      exact hTa.differentiableAt.hasDerivAt
    have hz : HasDerivAt (fun s => C'.ζ (C.bdry s))
        (deriv (C'.ζ ∘ C.ζ.symm) (C.ζ (C.bdry s)) * C.R.loop' s) s := hTd.comp s hγ
    have h2 := (hΨ' _ (hover s hsI).2).comp s hz
    have he := C.toAnalyticCoord.coeff_transition C'.toAnalyticCoord hsrc hsrc' η
    rw [hval] at he
    have hc : coeffIn C.ζ η (C.R.loop s) * C.R.loop' s =
        coeffIn C'.ζ η (C'.ζ (C.bdry s)) *
          (deriv (C'.ζ ∘ C.ζ.symm) (C.ζ (C.bdry s)) * C.R.loop' s) := by
      rw [he, hval]
      ring
    have hsub := h1.sub h2
    rw [hc, sub_self] at hsub
    exact hsub
  refine ⟨D a, ?_⟩
  intro s hs
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.1
    (hDc.mono (Icc_subset_Icc le_rfl hs.2))
    (fun u hu => hDd u ⟨hu.1, hu.2.trans_le hs.2⟩)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℂ)) volume a s)
  rw [intervalIntegral.integral_zero] at he
  exact sub_eq_zero.mp he.symm

end
end Dubon2026.SourceFunctionField.CellGeometry
