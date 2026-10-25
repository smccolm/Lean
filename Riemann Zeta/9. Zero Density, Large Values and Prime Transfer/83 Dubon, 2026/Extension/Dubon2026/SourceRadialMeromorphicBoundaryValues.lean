import Dubon2026.SourceRadialMeromorphicCellPrimitives
import Dubon2026.SourceComplexResidueSubtractedCoefficient
import Dubon2026.SourceCellBoundaryDifferentiation

/-! DUB-17/18 -> cover Abel converse -> meromorphic loop generation.
Restore the residue logarithm along the actual radial boundary. Its increment
is the residue period and its derivative is the original coefficient integral.
Adapted from the existing original-curve proof, originating in
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialMeromorphicPeriods
noncomputable section
open Set Complex
open scoped Real
variable {X R : Type*} [TopologicalSpace X]

/-- The continuous logarithm of the radial displacement along its parameter. -/
def logTerm {D : RadialCellDissection X} (C : D.ιC) (s : ℝ) : ℂ :=
  Real.log ((D.cell C).R.r s) + s * I

/-- Boundary primitive including the exact simple-pole logarithmic term. -/
def hfun {D : RadialCellDissection X} (S : Finset (X)) (residue : X → R → ℂ)
    (Ψ : R → D.ιC → ℂ → ℂ) (C : D.ιC) (s : ℝ) : R → ℂ :=
  fun r => Ψ r C ((D.cell C).R.loop s) + ρ D S residue C r * logTerm C s

theorem logTerm_add_two_pi {D : RadialCellDissection X} (C : D.ιC) (s : ℝ) :
    logTerm C (s + 2 * π) = logTerm C s + 2 * π * I := by
  simp only [logTerm, (D.cell C).R.hper s]
  push_cast
  ring

theorem hfun_add_two_pi {D : RadialCellDissection X} (S : Finset (X))
    (residue : X → R → ℂ) (Ψ : R → D.ιC → ℂ → ℂ) (C : D.ιC) (s : ℝ) :
    hfun S residue Ψ C (s + 2 * π) = hfun S residue Ψ C s + (2 * π * I) • ρ D S residue C := by
  funext r
  simp only [hfun, (D.cell C).R.loop_periodic s, logTerm_add_two_pi, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

theorem continuous_logTerm {D : RadialCellDissection X} (C : D.ιC) : Continuous (logTerm C) := by
  unfold logTerm
  refine (continuous_ofReal.comp ?_).add (by fun_prop)
  exact (D.cell C).R.hcont.log fun s => ((D.cell C).R.hpos s).ne'

theorem hasDerivAt_logTerm {D : RadialCellDissection X} (C : D.ιC) (k : Fin (D.cell C).R.N)
    {s : ℝ} (hs : s ∈ Ioo ((D.cell C).R.φs k.castSucc) ((D.cell C).R.φs k.succ)) :
    HasDerivAt (logTerm C)
      ((D.cell C).R.loop' s / ((D.cell C).R.loop s - (D.cell C).R.q)) s := by
  have hr := (D.cell C).R.hasDerivAt_radiusOnArc k hs
  have hr0 : (D.cell C).R.r s ≠ 0 := ((D.cell C).R.hpos s).ne'
  have h1 := (hr.log hr0).ofReal_comp
  have h2 : HasDerivAt (fun s : ℝ => (s : ℂ) * I) (1 * I) s :=
    (hasDerivAt_id s).ofReal_comp.mul_const I
  refine (h1.add h2).congr_deriv ?_
  rw [(D.cell C).R.loop'_eq_loopDerivOnArc k hs, (D.cell C).R.loop_sub_center,
    RadialRegion.loopDerivOnArc]
  have he : exp (s * I) ≠ 0 := exp_ne_zero _
  have hr0' : ((D.cell C).R.r s : ℂ) ≠ 0 := by exact_mod_cast hr0
  push_cast
  field_simp

theorem hasDerivAt_hfun {D : RadialCellDissection X} (S : Finset (X))
    (residue : X → R → ℂ) {V : D.ιC → Set ℂ} {Ψ : R → D.ιC → ℂ → ℂ}
    (f : R → D.ιC → ℂ → ℂ)
    (hP : RegPrimData D S (fun r C =>
      residueSubtractedCoefficient (D.cell C).R.q (ρ D S residue C r) (f r C)) V Ψ) (r : R) (C : D.ιC) (k : Fin (D.cell C).R.N) {s : ℝ}
    (hs : s ∈ Ioo ((D.cell C).R.φs k.castSucc) ((D.cell C).R.φs k.succ)) :
    HasDerivAt (fun s => hfun S residue Ψ C s r) (f r C ((D.cell C).R.loop s) * (D.cell C).R.loop' s) s := by
  have hγ := (D.cell C).R.hasDerivAt_loop k hs
  have hls := hP.hKV C ((D.cell C).R.loop_mem_K s)
  have hne := (D.cell C).R.loop_ne_center s
  have h1 := (hP.hΨ r C _ hls).comp s hγ
  have h2 := (hasDerivAt_logTerm C k hs).const_mul (ρ D S residue C r)
  refine (h1.add h2).congr_deriv ?_
  change (residueSubtractedCoefficient (D.cell C).R.q (ρ D S residue C r) (f r C) ((D.cell C).R.loop s)) * (D.cell C).R.loop' s + ρ D S residue C r * ((D.cell C).R.loop' s / ((D.cell C).R.loop s - (D.cell C).R.q)) = _
  rw [residueSubtractedCoefficient_of_ne _ _ _ hne]
  have hne' := sub_ne_zero.mpr hne
  field_simp
  ring

theorem continuous_hfun {D : RadialCellDissection X} (S : Finset (X))
    (residue : X → R → ℂ) {V : D.ιC → Set ℂ} {Ψ : R → D.ιC → ℂ → ℂ}
    (f : R → D.ιC → ℂ → ℂ)
    (hP : RegPrimData D S (fun r C =>
      residueSubtractedCoefficient (D.cell C).R.q (ρ D S residue C r) (f r C)) V Ψ) (r : R) (C : D.ιC) :
    Continuous fun s => hfun S residue Ψ C s r := by
  have h1 : Continuous fun s => Ψ r C ((D.cell C).R.loop s) := by
    refine continuous_iff_continuousAt.mpr fun s => ?_
    exact (hP.hΨ r C _ (hP.hKV C ((D.cell C).R.loop_mem_K s))).continuousAt.comp
      (D.cell C).R.continuous_loop.continuousAt
  exact h1.add (continuous_const.mul (continuous_logTerm C))

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialMeromorphicPeriods
