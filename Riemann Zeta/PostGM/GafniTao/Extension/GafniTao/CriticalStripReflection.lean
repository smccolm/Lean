import GafniTao.ZeroEnergy

/-!
# Critical-strip reflection at the local-count layer

This module isolates the functional-equation facts needed before the moment
modules are imported.  In particular, local unit-bin counts may reflect the
left half of the critical strip without creating a dependency cycle through
the refined exponent assembly.
-/

namespace GafniTao

open Complex Filter
open RiemannZeta.GuthMaynard

/-- Reflection through the critical line. -/
noncomputable def criticalStripReflect (z : ℂ) : ℂ := 1 - z

private theorem analyticOrderAt_riemannZeta_eq_completedRiemannZeta
    {z : ℂ} (hzRe : 0 < z.re) (hzUpper : z.re < 1) :
    analyticOrderAt riemannZeta z = analyticOrderAt completedRiemannZeta z := by
  have hz0 : z ≠ 0 := by
    intro hz
    subst z
    norm_num at hzRe
  have hz1 : z ≠ 1 := by
    intro hz
    subst z
    norm_num at hzUpper
  have hZeta : AnalyticAt ℂ riemannZeta z :=
    analyticOn_riemannZeta z (by simpa using hz1)
  have hCompleted : AnalyticAt ℂ completedRiemannZeta z := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    have hAwayZero : ({0}ᶜ : Set ℂ) ∈ nhds z :=
      isOpen_compl_singleton.mem_nhds (by simpa using hz0)
    have hAwayOne : ({1}ᶜ : Set ℂ) ∈ nhds z :=
      isOpen_compl_singleton.mem_nhds (by simpa using hz1)
    filter_upwards [hAwayZero, hAwayOne] with s hs0 hs1
    exact differentiableAt_completedZeta (by simpa using hs0) (by simpa using hs1)
  have hGammaInv : AnalyticAt ℂ (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) z := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    exact Filter.Eventually.of_forall fun _ =>
      Complex.differentiable_Gammaℝ_inv.differentiableAt
  have hEventually :
      riemannZeta =ᶠ[nhds z]
        completedRiemannZeta * fun s : ℂ => (Complex.Gammaℝ s)⁻¹ := by
    have hAwayZero : ({0}ᶜ : Set ℂ) ∈ nhds z :=
      isOpen_compl_singleton.mem_nhds (by simpa using hz0)
    filter_upwards [hAwayZero] with s hs
    have hs0 : s ≠ 0 := by simpa using hs
    simp only [Pi.mul_apply]
    rw [riemannZeta_def_of_ne_zero hs0]
    simp [div_eq_mul_inv]
  calc
    analyticOrderAt riemannZeta z =
        analyticOrderAt
          (completedRiemannZeta * fun s : ℂ => (Complex.Gammaℝ s)⁻¹) z :=
      analyticOrderAt_congr hEventually
    _ = analyticOrderAt completedRiemannZeta z +
        analyticOrderAt (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) z :=
      analyticOrderAt_mul hCompleted hGammaInv
    _ = analyticOrderAt completedRiemannZeta z + 0 := by
      rw [hGammaInv.analyticOrderAt_eq_zero.2]
      exact inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hzRe)
    _ = analyticOrderAt completedRiemannZeta z := by simp

private theorem analyticOrderAt_completedRiemannZeta_reflect
    (z : ℂ) :
    analyticOrderAt completedRiemannZeta (criticalStripReflect z) =
      analyticOrderAt completedRiemannZeta z := by
  have hReflectAnalytic : AnalyticAt ℂ criticalStripReflect z := by
    unfold criticalStripReflect
    fun_prop
  have hReflectDeriv : deriv criticalStripReflect z = -1 := by
    have h := (hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)
    have h' : HasDerivAt criticalStripReflect (-1) z := by
      simpa only [criticalStripReflect, id_eq, zero_sub] using h
    exact h'.deriv
  have hComp := analyticOrderAt_comp_of_deriv_ne_zero
    (f := completedRiemannZeta) hReflectAnalytic (by simp [hReflectDeriv])
  have hFunction : completedRiemannZeta ∘ criticalStripReflect =
      completedRiemannZeta := by
    funext s
    exact completedRiemannZeta_one_sub s
  rw [hFunction] at hComp
  exact hComp.symm

/-- Reflection preserves analytic multiplicity for zeros in the open
critical strip. -/
theorem zeroMultiplicity_criticalStripReflect
    {z : ℂ} (hzRe : 0 < z.re) (hzUpper : z.re < 1) :
    zeroMultiplicity (criticalStripReflect z) = zeroMultiplicity z := by
  have hrefRe : 0 < (criticalStripReflect z).re := by
    simp [criticalStripReflect]
    linarith
  have hrefUpper : (criticalStripReflect z).re < 1 := by
    simp [criticalStripReflect]
    linarith
  unfold zeroMultiplicity analyticVanishingOrder
  apply congrArg ENat.toNat
  calc
    analyticOrderAt riemannZeta (criticalStripReflect z) =
        analyticOrderAt completedRiemannZeta (criticalStripReflect z) :=
      analyticOrderAt_riemannZeta_eq_completedRiemannZeta hrefRe hrefUpper
    _ = analyticOrderAt completedRiemannZeta z :=
      analyticOrderAt_completedRiemannZeta_reflect z
    _ = analyticOrderAt riemannZeta z :=
      (analyticOrderAt_riemannZeta_eq_completedRiemannZeta hzRe hzUpper).symm

/-- The functional equation sends every zero in the open critical strip to
the reflected zero. -/
theorem riemannZeta_criticalStripReflect_eq_zero
    {z : ℂ} (hzRe : 0 < z.re) (hzUpper : z.re < 1)
    (hzZero : riemannZeta z = 0) :
    riemannZeta (criticalStripReflect z) = 0 := by
  have hzNat : ∀ n : ℕ, z ≠ -n := by
    intro n h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hzOne : z ≠ 1 := by
    intro h
    subst z
    norm_num at hzUpper
  simpa [criticalStripReflect, hzZero] using riemannZeta_one_sub hzNat hzOne

/-- A zeta zero in the closed source strip is not on its left boundary. -/
theorem zero_re_pos_of_nonneg
    {z : ℂ} (hzNonneg : 0 ≤ z.re) (hzUpper : z.re ≤ 1)
    (hzZero : riemannZeta z = 0) :
    0 < z.re := by
  by_contra hzNotPos
  have hzRe : z.re = 0 := le_antisymm (le_of_not_gt hzNotPos) hzNonneg
  have hzNotZero : z ≠ 0 := by
    intro hz
    subst z
    rw [riemannZeta_zero] at hzZero
    norm_num at hzZero
  have hzNat : ∀ n : ℕ, z ≠ -n := by
    intro n h
    have hre := congrArg Complex.re h
    simp [hzRe] at hre
    have hn : n = 0 := by omega
    subst n
    apply hzNotZero
    simpa using h
  have hzOne : z ≠ 1 := by
    intro h
    subst z
    norm_num at hzRe
  have hrefZero : riemannZeta (1 - z) = 0 := by
    simpa [hzZero] using riemannZeta_one_sub hzNat hzOne
  exact riemannZeta_ne_zero_of_one_le_re (s := 1 - z) (by simp [hzRe]) hrefZero

/-- A zeta zero in the closed source strip is not on its right boundary. -/
theorem zero_re_lt_one_of_le_one
    {z : ℂ} (hzUpper : z.re ≤ 1) (hzZero : riemannZeta z = 0) :
    z.re < 1 := by
  exact lt_of_le_of_ne hzUpper fun h =>
    riemannZeta_ne_zero_of_one_le_re (s := z) (by linarith) hzZero

end GafniTao
