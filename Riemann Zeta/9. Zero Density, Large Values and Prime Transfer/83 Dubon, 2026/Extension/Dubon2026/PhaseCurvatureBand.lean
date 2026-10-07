import Dubon2026.PhaseFirstDerivative
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

/-! # Quantitative control of the actual small-frequency interval -/

namespace Dubon2026

open Set

/-- A strictly negative derivative bounds the length of every actual frequency band. -/
theorem frequency_band_length_le {ν : ℝ → ℝ} (hν : Differentiable ℝ ν)
    {a b l r δ lam : ℝ} (hδ : 0 < δ) (hl : l ∈ Icc a b) (hr : r ∈ Icc a b) (hlr : l ≤ r)
    (hcurv : ∀ t ∈ Icc a b, deriv ν t ≤ -δ) (hlv : ν l ≤ lam) (hrv : -lam ≤ ν r) :
    r - l ≤ 2 * lam / δ := by
  have hd := (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le hν.continuous.continuousOn
    hν.differentiableOn (fun t ht => hcurv t (interior_subset ht)) l hl r hr hlr
  apply (le_div_iff₀ hδ).mpr
  nlinarith

/-- For a decreasing continuous frequency that crosses the central band, actual endpoints split
it into a positive-frequency tail, the small-frequency band, and a negative-frequency tail. -/
theorem exists_frequency_band_endpoints {ν : ℝ → ℝ} (hν : Continuous ν)
    {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam) (hmono : AntitoneOn ν (Icc a b))
    (ha : -lam < ν a) (hb : ν b < lam) :
    ∃ l r : ℝ, l ∈ Icc a b ∧ r ∈ Icc a b ∧ l ≤ r ∧ ν l ≤ lam ∧ -lam ≤ ν r ∧
      (l = a ∨ ν l = lam) ∧ (r = b ∨ ν r = -lam) := by
  have hl : ∃ l : ℝ, l ∈ Icc a b ∧ ν l ≤ lam ∧ -lam < ν l ∧ (l = a ∨ ν l = lam) := by
    by_cases h : ν a ≤ lam
    · exact ⟨a, ⟨le_rfl, hab⟩, h, ha, Or.inl rfl⟩
    · obtain ⟨l, hl, he⟩ := intermediate_value_Icc' hab hν.continuousOn
        (show lam ∈ Icc (ν b) (ν a) from ⟨hb.le, le_of_not_ge h⟩)
      exact ⟨l, hl, he.le, by rw [he]; linarith, Or.inr he⟩
  have hr : ∃ r : ℝ, r ∈ Icc a b ∧ -lam ≤ ν r ∧ ν r < lam ∧ (r = b ∨ ν r = -lam) := by
    by_cases h : -lam ≤ ν b
    · exact ⟨b, ⟨hab, le_rfl⟩, h, hb, Or.inl rfl⟩
    · obtain ⟨r, hr, he⟩ := intermediate_value_Icc' hab hν.continuousOn
        (show -lam ∈ Icc (ν b) (ν a) from ⟨le_of_not_ge h, ha.le⟩)
      exact ⟨r, hr, he.ge, by rw [he]; linarith, Or.inr he⟩
  obtain ⟨l, hl, hlv, hlv', hle⟩ := hl
  obtain ⟨r, hr, hrv, hrv', hre⟩ := hr
  have hlr : l ≤ r := by
    rcases hle with rfl | hle
    · exact hr.1
    rcases hre with rfl | hre
    · exact hl.2
    by_contra h
    have hh := hmono hr hl (le_of_not_ge h)
    rw [hle, hre] at hh
    linarith
  exact ⟨l, r, hl, hr, hlr, hlv, hrv, hle, hre⟩

end Dubon2026
