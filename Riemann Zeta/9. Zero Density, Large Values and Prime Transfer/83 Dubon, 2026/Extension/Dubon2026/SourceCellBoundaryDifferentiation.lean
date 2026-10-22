import Dubon2026.SourceCellBoundaryGeometry
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! DUB-17/18 -> raw reciprocity -> centered cell residue contour.
Each source C2 radial arc has a continuous extension of its derivative. On the
open arc it equals the genuine derivative of the actual boundary loop. Endpoint
values will be handled by almost-everywhere interval-integral congruence.
Adapted from S_Complex_integral_radial_loop_eq_two_pi_I_mul_sum_residue,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialRegion
noncomputable section
open Complex Set
variable (R : RadialRegion)

/-- A continuous extension of the within derivative on one closed radial arc. -/
def radiusDerivOnArc (k : Fin R.N) (φ : ℝ) : ℝ :=
  derivWithin R.r (R.arcIcc k)
    (projIcc (R.φs k.castSucc) (R.φs k.succ) (R.hmono Fin.castSucc_lt_succ).le φ : ℝ)

theorem continuous_radiusDerivOnArc (k : Fin R.N) : Continuous (R.radiusDerivOnArc k) :=
  ((R.hC2 k).continuousOn_derivWithin (uniqueDiffOn_Icc (R.hmono Fin.castSucc_lt_succ))
    (by norm_num)).comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      fun φ => (projIcc _ _ (R.hmono Fin.castSucc_lt_succ).le φ).2

theorem hasDerivAt_radiusOnArc (k : Fin R.N) {φ : ℝ}
    (hφ : φ ∈ Ioo (R.φs k.castSucc) (R.φs k.succ)) :
    HasDerivAt R.r (R.radiusDerivOnArc k φ) φ := by
  have hm : φ ∈ R.arcIcc k := ⟨hφ.1.le, hφ.2.le⟩
  have hd : DifferentiableAt ℝ R.r φ :=
    ((R.hC2 k).differentiableOn (by norm_num)).differentiableAt (Icc_mem_nhds hφ.1 hφ.2)
  have he : R.radiusDerivOnArc k φ = deriv R.r φ := by
    rw [radiusDerivOnArc, projIcc_of_mem _ hm]
    exact hd.derivWithin (uniqueDiffOn_Icc (R.hmono Fin.castSucc_lt_succ) φ hm)
  rw [he]
  exact hd.hasDerivAt

/-- The continuous extension of the boundary derivative on one radial arc. -/
def loopDerivOnArc (k : Fin R.N) (φ : ℝ) : ℂ :=
  ((R.radiusDerivOnArc k φ : ℂ) + R.r φ * I) * exp (φ * I)

theorem continuous_loopDerivOnArc (k : Fin R.N) : Continuous (R.loopDerivOnArc k) := by
  have h1 := R.continuous_radiusDerivOnArc k
  have h2 := R.hcont
  unfold loopDerivOnArc
  fun_prop

theorem loop'_eq_loopDerivOnArc (k : Fin R.N) {φ : ℝ}
    (hφ : φ ∈ Ioo (R.φs k.castSucc) (R.φs k.succ)) : R.loop' φ = R.loopDerivOnArc k φ := by
  rw [loop', loopDerivOnArc, (R.hasDerivAt_radiusOnArc k hφ).deriv]

theorem hasDerivAt_loop (k : Fin R.N) {φ : ℝ}
    (hφ : φ ∈ Ioo (R.φs k.castSucc) (R.φs k.succ)) : HasDerivAt R.loop (R.loop' φ) φ := by
  have hr : HasDerivAt (fun s => (R.r s : ℂ)) ((deriv R.r φ : ℝ) : ℂ) φ := by
    have h := R.hasDerivAt_radiusOnArc k hφ
    rw [← h.deriv] at h
    exact h.ofReal_comp
  have he : HasDerivAt (fun s : ℝ => exp (s * I)) (exp (φ * I) * I) φ := by
    have h := (hasDerivAt_id φ).ofReal_comp.mul_const I
    simpa only [Complex.ofReal_one, one_mul] using (Complex.hasDerivAt_exp ((φ : ℂ) * I)).comp φ h
  refine ((hr.mul he).const_add R.q).congr_deriv ?_
  rw [loop']
  ring

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialRegion
