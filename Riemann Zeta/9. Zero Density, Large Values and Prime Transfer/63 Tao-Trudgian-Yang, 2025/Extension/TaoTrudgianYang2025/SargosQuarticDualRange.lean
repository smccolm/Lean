import TaoTrudgianYang2025.SargosQuarticLegendreScale
import Mathlib.Analysis.Calculus.MeanValue

/-! Exact dual slope interval and the source-scale residual's Lipschitz control. -/

noncomputable section

open Set

namespace TaoTrudgianYang2025

theorem sargosQuarticSlopeRange_eq {N α γ : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2)) :
    sargosQuarticSlopeRange N α γ =
      Ioo (sargosQuarticSlope α γ N) (sargosQuarticSlope α γ (2*N)) := by
  have hm := sargosQuarticSlope_strictMonoOn hN hα hγ
  have hNN : N ≤ 2*N := by linarith
  apply Set.Subset.antisymm
  · rintro y ⟨x,hx,rfl⟩
    have hxc : x ∈ Icc N (2*N) := ⟨hx.1.le,hx.2.le⟩
    exact ⟨hm ⟨le_rfl,hNN⟩ hxc hx.1,hm hxc ⟨hNN,le_rfl⟩ hx.2⟩
  · exact intermediate_value_Ioo hNN (contDiff_sargosQuarticSlope α γ).continuous.continuousOn

theorem sargosQuarticSlopeRange_convex {N α γ : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2)) :
    Convex ℝ (sargosQuarticSlopeRange N α γ) := by
  rw [sargosQuarticSlopeRange_eq hN hα hγ]
  exact convex_Ioo _ _

theorem sargosQuartic_source_cubic_bound {N γ : ℝ}
    (hN : 0 < N) (hγ : |γ| ≤ 1/N^3) : |γ*N^3| ≤ 1 := by
  rw [abs_mul,abs_pow,abs_of_pos hN]
  calc
    _ ≤ (1/N^3)*N^3 := mul_le_mul_of_nonneg_right hγ (by positivity)
    _ = 1 := by field_simp

theorem sargosQuarticSlopeRange_source_subset {N α γ : ℝ}
    (hN : 9216 ≤ N) (hα : 1/Real.sqrt N ≤ α) (hγ : |γ| ≤ 1/N^3) :
    sargosQuarticSlopeRange N α γ ⊆ Ioo (2*α*N-4) (4*α*N+32) := by
  have hN0 : 0 < N := by linarith
  rw [sargosQuarticSlopeRange_eq hN0 (sargosQuartic_source_scale hN hα).1
    (sargosQuartic_source_smallness hN hα hγ)]
  have hc := abs_le.mp (sargosQuartic_source_cubic_bound hN0 hγ)
  intro y hy
  simp only [mem_Ioo,sargosQuarticSlope] at hy ⊢
  constructor <;> nlinarith [hc.1,hc.2,hy.1,hy.2]

theorem sargosQuarticSlopeRange_dyadic_subset {N Δ α γ : ℝ}
    (hN : 9216 ≤ N) (hΔ : 1/Real.sqrt N ≤ Δ) (hα : α ∈ Icc Δ (2*Δ))
    (hγ : |γ| ≤ 1/N^3) :
    sargosQuarticSlopeRange N α γ ⊆ Ioo (2*Δ*N-4) (4*(2*Δ*N)+32) := by
  have hN0 : 0 < N := by linarith
  intro y hy
  have hh := sargosQuarticSlopeRange_source_subset hN (hΔ.trans hα.1) hγ hy
  constructor
  · exact lt_of_le_of_lt (by nlinarith [mul_le_mul_of_nonneg_right hα.1 hN0.le]) hh.1
  · exact lt_of_lt_of_le hh.2 (by nlinarith [mul_le_mul_of_nonneg_right hα.2 hN0.le])

theorem sargosQuarticLegendreRemainder_source_lipschitz {N α γ u v : ℝ}
    (hN : 9216 ≤ N) (hα : 1/Real.sqrt N ≤ α) (hγ : |γ| ≤ 1/N^3)
    (hu : u ∈ sargosQuarticSlopeRange N α γ) (hv : v ∈ sargosQuarticSlopeRange N α γ) :
    |sargosQuarticLegendreRemainder N α γ v-sargosQuarticLegendreRemainder N α γ u| ≤
      (16384/(α*N))*|v-u| := by
  have hc := sargosQuarticSlopeRange_convex (by linarith : 0 < N)
    (sargosQuartic_source_scale hN hα).1 (sargosQuartic_source_smallness hN hα hγ)
  have hd : ∀ x ∈ sargosQuarticSlopeRange N α γ,
      HasDerivWithinAt (sargosQuarticLegendreRemainder N α γ)
        (sargosQuarticLegendreRemainderDerivative N α γ x) (sargosQuarticSlopeRange N α γ) x :=
    fun x hx => (sargosQuarticLegendreRemainder_source_hasDerivAt hN hα hγ hx).1.hasDerivWithinAt
  have hb : ∀ x ∈ sargosQuarticSlopeRange N α γ,
      ‖sargosQuarticLegendreRemainderDerivative N α γ x‖ ≤ 16384/(α*N) := by
    intro x hx
    simpa only [Real.norm_eq_abs] using
      sargosQuarticLegendreRemainderDerivative_source_bound hN hα hγ hx
  simpa only [Real.norm_eq_abs] using
    hc.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb hu hv

end TaoTrudgianYang2025

