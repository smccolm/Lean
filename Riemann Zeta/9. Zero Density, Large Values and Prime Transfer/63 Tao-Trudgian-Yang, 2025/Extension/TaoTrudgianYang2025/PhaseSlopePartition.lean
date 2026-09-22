import TaoTrudgianYang2025.BetaWeightedPhase
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Quantitative slope partitions

The two cut points are obtained from the actual continuous slope by the
intermediate value theorem. A strictly negative derivative bounds the
width of the transition interval; no stationary-point certificate is assumed.
-/

noncomputable section

open Set
open scoped ContDiff

namespace TaoTrudgianYang2025

theorem slope_drop_of_deriv_le {f : ℝ → ℝ} {a b m : ℝ}
    (hf : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
    (hd : ∀ x ∈ Icc a b, deriv f x ≤ -m)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
    m*(y-x) ≤ f x-f y := by
  have h := (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le
    (fun z hz => (hf z hz).continuousAt.continuousWithinAt)
    (fun z hz => (hf z (interior_subset hz)).differentiableWithinAt)
    (fun z hz => hd z (interior_subset hz)) x hx y hy hxy
  linarith

theorem exists_slope_transition_partition {f : ℝ → ℝ} {a b lam : ℝ}
    (hab : a ≤ b) (hlam : 0 ≤ lam) (hf : ContinuousOn f (Icc a b))
    (hlo : f b ≤ lam) (hhi : -lam ≤ f a) :
    ∃ c d : ℝ, a ≤ c ∧ c ≤ d ∧ d ≤ b ∧
      f c ≤ lam ∧ -lam ≤ f d ∧
      (c = a ∨ f c = lam) ∧ (d = b ∨ f d = -lam) := by
  obtain ⟨c,hac,hcb,hclo,hchi,hc⟩ :
      ∃ c : ℝ, a ≤ c ∧ c ≤ b ∧ -lam ≤ f c ∧ f c ≤ lam ∧
        (c = a ∨ f c = lam) := by
    by_cases ha : f a ≤ lam
    · exact ⟨a,le_rfl,hab,hhi,ha,Or.inl rfl⟩
    · obtain ⟨c,hc,hfc⟩ := intermediate_value_Icc' hab hf
        (show lam ∈ Icc (f b) (f a) from ⟨hlo,le_of_not_ge ha⟩)
      exact ⟨c,hc.1,hc.2,by linarith [hfc],hfc.le,Or.inr hfc⟩
  by_cases hb : -lam ≤ f b
  · exact ⟨c,b,hac,hcb,le_rfl,hchi,hb,hc,Or.inl rfl⟩
  · have hsub : Icc c b ⊆ Icc a b := fun x hx => ⟨hac.trans hx.1,hx.2⟩
    obtain ⟨d,hd,hfd⟩ := intermediate_value_Icc' hcb (hf.mono hsub)
      (show -lam ∈ Icc (f b) (f c) from ⟨le_of_not_ge hb,hclo⟩)
    exact ⟨c,d,hac,hd.1,hd.2,hchi,hfd.ge,hc,Or.inr hfd⟩

theorem slope_transition_width_le {f : ℝ → ℝ} {a b c d m lam : ℝ}
    (hm : 0 < m)
    (hf : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
    (hd : ∀ x ∈ Icc a b, deriv f x ≤ -m)
    (hc : c ∈ Icc a b) (he : d ∈ Icc a b) (hcd : c ≤ d)
    (hcl : f c ≤ lam) (hdl : -lam ≤ f d) :
    d-c ≤ 2*lam/m := by
  have hdrop := slope_drop_of_deriv_le hf hd hc he hcd
  apply (le_div_iff₀ hm).mpr
  nlinarith

end TaoTrudgianYang2025
