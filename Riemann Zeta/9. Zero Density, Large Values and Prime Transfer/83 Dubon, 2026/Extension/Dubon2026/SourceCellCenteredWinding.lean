import Dubon2026.SourceCellBoundaryDifferentiation
import Dubon2026.SourceCellArcFundamentalTheorem
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! DUB-17/18 -> raw reciprocity -> residue contour in a pole-centered cell.
The exact radial boundary has logarithmic integral 2*pi*I about its center.
Integrate log(radius)+I*angle on the existing finite smooth arcs and telescope;
positivity and periodicity of the radius discharge the logarithmic endpoint term.
No winding deformation or noncentral-pole theorem is needed for this consumer.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialRegion
noncomputable section
open Complex Set MeasureTheory
open scoped Real

theorem centered_winding (R : RadialRegion) :
    IntervalIntegrable (fun φ => R.loop' φ / (R.loop φ - R.q)) volume 0 (2 * π) ∧
      (∫ φ in (0 : ℝ)..(2 * π), R.loop' φ / (R.loop φ - R.q)) = 2 * π * I := by
  have hwi : ∀ φ, R.loop' φ / (R.loop φ - R.q) = ((deriv R.r φ / R.r φ : ℝ) : ℂ) + I := by
    intro φ
    have hr : (R.r φ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (R.hpos φ).ne'
    rw [loop', R.loop_sub_center]
    push_cast
    field_simp
  let F : ℝ → ℂ := fun φ => (Real.log (R.r φ) : ℂ) + (φ : ℂ) * I
  have hFc : Continuous F :=
    (continuous_ofReal.comp (R.hcont.log fun φ => (R.hpos φ).ne')).add
      (continuous_ofReal.mul continuous_const)
  have hd : ∀ k : Fin R.N, ∀ φ ∈ Ioo (R.φs k.castSucc) (R.φs k.succ),
      HasDerivAt F (R.loop' φ / (R.loop φ - R.q)) φ := by
    intro k φ hφ
    have hr := R.hasDerivAt_radiusOnArc k hφ
    have hl := (hr.log (R.hpos φ).ne').ofReal_comp
    have hi := (hasDerivAt_id φ).ofReal_comp.mul_const I
    rw [hwi φ, hr.deriv]
    simpa only [Complex.ofReal_one, one_mul] using hl.add hi
  have hext : ∀ k : Fin R.N, ∃ g : ℝ → ℂ, Continuous g ∧
      EqOn (fun φ => R.loop' φ / (R.loop φ - R.q)) g
        (Ioo (R.φs k.castSucc) (R.φs k.succ)) := by
    intro k
    refine ⟨fun φ => ((R.radiusDerivOnArc k φ / R.r φ : ℝ) : ℂ) + I, ?_, ?_⟩
    · exact (continuous_ofReal.comp ((R.continuous_radiusDerivOnArc k).div R.hcont
        (fun φ => (R.hpos φ).ne'))).add continuous_const
    · intro φ hφ
      dsimp only
      rw [hwi φ, (R.hasDerivAt_radiusOnArc k hφ).deriv]
  obtain ⟨hint, he⟩ := R.integral_eq_sub_of_arc_derivatives _ F hFc hd hext
  have hrper : R.r (2 * π) = R.r 0 := by simpa only [zero_add] using R.hper 0
  have hval : F (2 * π) - F 0 = 2 * π * I := by
    dsimp only [F]
    rw [hrper]
    push_cast
    ring
  exact ⟨hint, he.trans hval⟩

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialRegion
