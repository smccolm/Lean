import Dubon2026.RadialInnerIntegrals

/-! # A three-region integral estimate with all integrability obligations discharged -/

namespace Dubon2026

open MeasureTheory Set

theorem nonnegative_three_region_integral {f g h j : ℝ → ℝ} {a B : ℝ}
    (hf : Continuous f) (hf0 : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ f r)
    (ha : 0 ≤ a) (haB : a ≤ B)
    (hg : IntegrableOn g (Ioi (0 : ℝ))) (hg0 : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ g r)
    (hh : IntegrableOn h (Ioc (0 : ℝ) B)) (hh0 : ∀ r ∈ Ioc (0 : ℝ) B, 0 ≤ h r)
    (hj : IntegrableOn j (Ioi B))
    (hnear : ∀ r ∈ Ioc (0 : ℝ) a, f r ≤ g r)
    (hmiddle : ∀ r ∈ Ioc a B, f r ≤ h r)
    (htail : ∀ r ∈ Ioi B, f r ≤ j r) :
    IntegrableOn f (Ioi (0 : ℝ)) ∧
      (∫ r in Ioi (0 : ℝ), f r) ≤
        (∫ r in Ioi (0 : ℝ), g r) + (∫ r in Ioc (0 : ℝ) B, h r) + ∫ r in Ioi B, j r := by
  have hB : 0 ≤ B := ha.trans haB
  have hfi : IntegrableOn f (Ioi B) := hj.mono' hf.aestronglyMeasurable (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 r (hB.trans_lt hr))]
    exact htail r hr)
  have hfIoc (l u : ℝ) : IntegrableOn f (Ioc l u) :=
    hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hfall : IntegrableOn f (Ioi (0 : ℝ)) := by
    rw [← Ioc_union_Ioi_eq_Ioi hB]
    exact (hfIoc 0 B).union hfi
  have hsub : Ioc a B ⊆ Ioc (0 : ℝ) B := fun r hr => ⟨ha.trans_lt hr.1, hr.2⟩
  have h1 : (∫ r in Ioc (0 : ℝ) a, f r) ≤ ∫ r in Ioi (0 : ℝ), g r := by
    apply (setIntegral_mono_on (hfIoc 0 a) (hg.mono_set Ioc_subset_Ioi_self)
      measurableSet_Ioc hnear).trans
    exact setIntegral_mono_set hg (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact hg0 r hr) (Filter.Eventually.of_forall Ioc_subset_Ioi_self)
  have h2 : (∫ r in Ioc a B, f r) ≤ ∫ r in Ioc (0 : ℝ) B, h r := by
    apply (setIntegral_mono_on (hfIoc a B) (hh.mono_set hsub) measurableSet_Ioc hmiddle).trans
    exact setIntegral_mono_set hh (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact hh0 r hr) (Filter.Eventually.of_forall hsub)
  have h3 : (∫ r in Ioi B, f r) ≤ ∫ r in Ioi B, j r :=
    setIntegral_mono_on hfi hj measurableSet_Ioi htail
  refine ⟨hfall, ?_⟩
  have he := intervalIntegral.integral_interval_add_Ioi' (hf.intervalIntegrable 0 B) hfi
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable 0 a) (hf.intervalIntegrable a B),
    intervalIntegral.integral_of_le ha, intervalIntegral.integral_of_le haB] at he
  rw [← he]
  exact add_le_add (add_le_add h1 h2) h3

end Dubon2026
