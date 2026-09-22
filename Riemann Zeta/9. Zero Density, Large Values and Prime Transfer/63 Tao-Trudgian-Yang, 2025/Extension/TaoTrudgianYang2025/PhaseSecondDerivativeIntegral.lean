import TaoTrudgianYang2025.PhaseSlopePartition

/-!
# A second-derivative bound for actual Fourier-character integrals

The proof partitions the actual slope at plus and minus a positive threshold.
The central interval is bounded by its length; both outer intervals use the
checked first-derivative estimate. The threshold is then optimized at sqrt m.
-/

noncomputable section

open Set MeasureTheory
open scoped ContDiff FourierTransform

namespace TaoTrudgianYang2025

theorem norm_fourierCharIntegral_le_of_curvature_threshold
    {φ : ℝ → ℝ} {a b m lam : ℝ}
    (hab : a ≤ b) (hm : 0 < m) (hlam : 0 < lam)
    (hφ : ∀ x ∈ Icc a b, ContDiffAt ℝ 2 φ x)
    (hcurv : ∀ x ∈ Icc a b, deriv (deriv φ) x ≤ -m) :
    ‖∫ x in a..b, (𝐞 (φ x) : ℂ)‖ ≤ 2/(lam*Real.pi)+2*lam/m := by
  have hdiff : ∀ x ∈ Icc a b, DifferentiableAt ℝ (deriv φ) x := by
    intro x hx
    exact ((hφ x hx).derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hcont : ContinuousOn (deriv φ) (Icc a b) :=
    fun x hx => (hdiff x hx).continuousAt.continuousWithinAt
  have hmono : AntitoneOn (deriv φ) (Icc a b) := by
    intro x hx y hy hxy
    have h := slope_drop_of_deriv_le hdiff hcurv hx hy hxy
    have hp : 0 ≤ m*(y-x) := mul_nonneg hm.le (sub_nonneg.mpr hxy)
    linarith
  have hcost : 1/(lam*Real.pi) ≤ 2/(lam*Real.pi)+2*lam/m := by
    have hp : 0 ≤ 1/(lam*Real.pi) := by positivity
    have hq : 0 ≤ 2*lam/m := by positivity
    calc
      _ ≤ 1/(lam*Real.pi)+1/(lam*Real.pi)+2*lam/m := by linarith
      _ = _ := by ring
  by_cases hb : lam ≤ deriv φ b
  · apply (norm_fourierCharIntegral_le_of_slope_gap hab hlam hφ hmono
      (Or.inl (fun x hx => hb.trans (hmono hx ⟨hab,le_rfl⟩ hx.2)))).trans hcost
  by_cases ha : deriv φ a ≤ -lam
  · apply (norm_fourierCharIntegral_le_of_slope_gap hab hlam hφ hmono
      (Or.inr (fun x hx => (hmono ⟨le_rfl,hab⟩ hx hx.1).trans ha))).trans hcost
  obtain ⟨c,d,hac,hcd,hdb,hcl,hdl,hc,hd⟩ :=
    exists_slope_transition_partition hab hlam.le hcont
      (le_of_not_ge hb) (le_of_not_ge ha)
  have hcb : c ≤ b := hcd.trans hdb
  have had : a ≤ d := hac.trans hcd
  have hwidth := slope_transition_width_le hm hdiff hcurv
    (show c ∈ Icc a b from ⟨hac,hcb⟩)
    (show d ∈ Icc a b from ⟨had,hdb⟩) hcd hcl hdl
  have hleft : ‖∫ x in a..c, (𝐞 (φ x) : ℂ)‖ ≤ 1/(lam*Real.pi) := by
    rcases hc with rfl | hc
    · simp only [intervalIntegral.integral_same,norm_zero]
      positivity
    · have hs : Icc a c ⊆ Icc a b := fun x hx => ⟨hx.1,hx.2.trans hcb⟩
      apply norm_fourierCharIntegral_le_of_slope_gap hac hlam
        (fun x hx => hφ x (hs hx))
        (fun x hx y hy hxy => hmono (hs hx) (hs hy) hxy)
      exact Or.inl (fun x hx => by
        rw [← hc]
        exact hmono (hs hx) ⟨hac,hcb⟩ hx.2)
  have hright : ‖∫ x in d..b, (𝐞 (φ x) : ℂ)‖ ≤ 1/(lam*Real.pi) := by
    rcases hd with rfl | hd
    · simp only [intervalIntegral.integral_same,norm_zero]
      positivity
    · have hs : Icc d b ⊆ Icc a b := fun x hx => ⟨had.trans hx.1,hx.2⟩
      apply norm_fourierCharIntegral_le_of_slope_gap hdb hlam
        (fun x hx => hφ x (hs hx))
        (fun x hx y hy hxy => hmono (hs hx) (hs hy) hxy)
      exact Or.inr (fun x hx => by
        rw [← hd]
        exact hmono ⟨had,hdb⟩ (hs hx) hx.1)
  have hmid : ‖∫ x in c..d, (𝐞 (φ x) : ℂ)‖ ≤ d-c := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := c) (b := d) (C := 1) (f := fun x => (𝐞 (φ x) : ℂ))
      (fun x _ => by simp)
    simpa only [one_mul,abs_of_nonneg (sub_nonneg.mpr hcd)] using h
  have hi {u v : ℝ} (hu : a ≤ u) (huv : u ≤ v) (hv : v ≤ b) :
      IntervalIntegrable (fun x => (𝐞 (φ x) : ℂ)) volume u v := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le huv]
    intro x hx
    have hcx := (hφ x ⟨hu.trans hx.1,hx.2.trans hv⟩).continuousAt
    exact (show ContinuousAt (fun x => (𝐞 (φ x) : ℂ)) x from by
      simp only [Real.fourierChar_apply]
      fun_prop).continuousWithinAt
  have he := intervalIntegral.integral_add_adjacent_intervals
    (hi (u := a) le_rfl hac hcb) (hi hac hcd hdb)
  have he' := intervalIntegral.integral_add_adjacent_intervals
    (hi (u := a) le_rfl had hdb) (hi had hdb le_rfl)
  rw [← he',← he]
  have hn := (norm_add_le
    ((∫ x in a..c, (𝐞 (φ x) : ℂ))+(∫ x in c..d, (𝐞 (φ x) : ℂ)))
    (∫ x in d..b, (𝐞 (φ x) : ℂ))).trans
      (add_le_add (norm_add_le _ _) le_rfl)
  have htwo : 2/(lam*Real.pi) = 1/(lam*Real.pi)+1/(lam*Real.pi) := by ring
  rw [htwo]
  linarith

theorem norm_fourierCharIntegral_le_of_negative_curvature
    {φ : ℝ → ℝ} {a b m : ℝ}
    (hab : a ≤ b) (hm : 0 < m)
    (hφ : ∀ x ∈ Icc a b, ContDiffAt ℝ 2 φ x)
    (hcurv : ∀ x ∈ Icc a b, deriv (deriv φ) x ≤ -m) :
    ‖∫ x in a..b, (𝐞 (φ x) : ℂ)‖ ≤ (2/Real.pi+2)/Real.sqrt m := by
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have h := norm_fourierCharIntegral_le_of_curvature_threshold hab hm hs hφ hcurv
  convert h using 1
  have he := Real.sq_sqrt hm.le
  field_simp
  nlinarith [Real.pi_pos]

end TaoTrudgianYang2025
