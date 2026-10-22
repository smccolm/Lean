import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! DUB-17/18 -> raw reciprocity -> paired-edge change of variables.
Native nonatomic interval identities remove the finitely many arc endpoints.
Native continuous-derivative substitution applies directly to the within
derivative on the closed source arc; a global derivative extension is unneeded.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
open Set MeasureTheory intervalIntegral
open scoped Interval

theorem arc_integral_eq_of_continuous_extension {a b : ℝ} (hab : a ≤ b)
    {f g : ℝ → ℂ} (hg : ContinuousOn g (Icc a b)) (he : EqOn f g (Ioo a b)) :
    IntervalIntegrable f volume a b ∧ (∫ s in a..b, f s) = ∫ s in a..b, g s := by
  constructor
  · rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab]
    have hi : IntegrableOn g (Ioo a b) volume := (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp
      (hg.intervalIntegrable_of_Icc hab)
    exact hi.congr_fun he.symm measurableSet_Ioo
  · simp only [integral_of_le hab, integral_Ioc_eq_integral_Ioo]
    exact setIntegral_congr_fun measurableSet_Ioo he

theorem integral_reversed_contDiff_arc {a b a' b' : ℝ} (hab' : a' < b')
    {ψ : ℝ → ℝ} (hc : ContDiffOn ℝ 1 ψ (Icc a' b'))
    (hm : MapsTo ψ (Icc a' b') (Icc a b)) (ha : ψ a' = b) (hb : ψ b' = a)
    {G : ℝ → ℂ} (hG : ContinuousOn G (Icc a b)) :
    (∫ t in a'..b', derivWithin ψ (Icc a' b') t • (G ∘ ψ) t) = -∫ s in a..b, G s := by
  have hsub : (∫ t in a'..b', derivWithin ψ (Icc a' b') t • (G ∘ ψ) t) =
      ∫ s in ψ a'..ψ b', G s := by
    refine integral_deriv_smul_comp'' (by simpa only [uIcc_of_le hab'.le] using hc.continuousOn)
      ?_ (by simpa only [uIcc_of_le hab'.le] using
        hc.continuousOn_derivWithin (uniqueDiffOn_Icc hab') le_rfl) ?_
    · intro t ht
      rw [min_eq_left hab'.le, max_eq_right hab'.le] at ht
      have hd := ((hc.differentiableOn one_ne_zero).differentiableAt
        (Icc_mem_nhds ht.1 ht.2)).hasDerivAt
      rw [hd.differentiableAt.derivWithin (uniqueDiffOn_Icc hab' t ⟨ht.1.le, ht.2.le⟩)]
      exact hd.hasDerivWithinAt
    · rw [uIcc_of_le hab'.le]
      exact hG.mono (mapsTo_iff_image_subset.mp hm)
  rw [ha, hb, integral_symm a b] at hsub
  exact hsub

end Dubon2026.SourceFunctionField.CellGeometry
