import TaoTrudgianYang2025.BetaTaylorJets

/-!
# Global smooth Taylor averages and quantitative remainder identities

These lemmas apply to the actual smooth zero-extended Morse weight.
The supplied derivative bounds concern the original function, not its remainder.
-/

noncomputable section

open Set
open scoped ContDiff

namespace TaoTrudgianYang2025

theorem segmentTaylorAverage_hasDerivAt_global
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (a x : ℝ) (k : ℕ) :
    HasDerivAt (segmentTaylorAverage f a k) (segmentTaylorAverage f a (k+1) x) x := by
  apply segmentTaylorAverage_hasDerivAt (l := min a x-1) (r := max a x+1)
    (fun _ _ => hf.contDiffAt)
  · exact ⟨by linarith [min_le_left a x],by linarith [le_max_left a x]⟩
  · exact ⟨by linarith [min_le_right a x],by linarith [le_max_right a x]⟩

theorem segmentTaylorAverage_contDiff_global
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (a : ℝ) (k : ℕ) :
    ContDiff ℝ ∞ (segmentTaylorAverage f a k) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have ha : a ∈ Ioo (min a x-1) (max a x+1) :=
    ⟨by linarith [min_le_left a x],by linarith [le_max_left a x]⟩
  have hx : x ∈ Ioo (min a x-1) (max a x+1) :=
    ⟨by linarith [min_le_right a x],by linarith [le_max_right a x]⟩
  exact (segmentTaylorAverage_contDiffOn (fun _ _ => hf.contDiffAt) ha k).contDiffAt
    (isOpen_Ioo.mem_nhds hx)

theorem abs_segmentTaylorAverage_le_global
    {f : ℝ → ℝ} {M : ℝ} (a x : ℝ) (k : ℕ)
    (hb : ∀ u : ℝ, |iteratedDeriv k f u| ≤ M) :
    |segmentTaylorAverage f a k x| ≤ M := by
  apply abs_segmentTaylorAverage_le (l := min a x-1) (r := max a x+1) ?_ ?_ k
    (fun u _ => hb u)
  · exact ⟨by linarith [min_le_left a x],by linarith [le_max_left a x]⟩
  · exact ⟨by linarith [min_le_right a x],by linarith [le_max_right a x]⟩

theorem segmentTaylorAverage_second_global
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (a x : ℝ) :
    (x-a)^2*segmentTaylorAverage (deriv (deriv f)) a 0 x =
      f x-f a-(x-a)*deriv f a := by
  apply segmentTaylorAverage_second (l := min a x-1) (r := max a x+1)
    (fun _ _ => hf.contDiffAt)
  · exact ⟨by linarith [min_le_left a x],by linarith [le_max_left a x]⟩
  · exact ⟨by linarith [min_le_right a x],by linarith [le_max_right a x]⟩

end TaoTrudgianYang2025
