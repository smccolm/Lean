import TaoTrudgianYang2025.SargosQuarticLegendreBounds

/-! Source-scale uniformity for the actual quartic residual.
The explicit large-scale threshold is 9216; no claim about the omitted bounded
range or the still-missing oscillatory B-transform is made here. -/

noncomputable section

open Set

namespace TaoTrudgianYang2025

theorem sargosQuartic_source_scale {N α : ℝ}
    (hN : 9216 ≤ N) (hα : 1/Real.sqrt N ≤ α) :
    0 < α ∧ 96 ≤ α*N ∧ 1 ≤ N*α^2 := by
  have hN0 : 0 < N := by linarith
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hs96 : 96 ≤ Real.sqrt N := by
    nlinarith [Real.sq_sqrt hN0.le,Real.sqrt_nonneg N]
  have ha : 0 < α := (div_pos (by norm_num) hs).trans_le hα
  have has : 1 ≤ α*Real.sqrt N := (div_le_iff₀ hs).mp hα
  refine ⟨ha,?_,?_⟩
  · calc
      96 ≤ Real.sqrt N := hs96
      _ ≤ (α*Real.sqrt N)*Real.sqrt N := by nlinarith
      _ = α*N := by rw [mul_assoc,← sq,Real.sq_sqrt hN0.le]
  · calc
      1 = (1:ℝ)^2 := by norm_num
      _ ≤ (α*Real.sqrt N)^2 := pow_le_pow_left₀ zero_le_one has 2
      _ = N*α^2 := by rw [mul_pow,Real.sq_sqrt hN0.le]; ring

theorem sargosQuartic_source_smallness {N α γ : ℝ}
    (hN : 9216 ≤ N) (hα : 1/Real.sqrt N ≤ α) (hγ : |γ| ≤ 1/N^3) :
    |γ| ≤ α/(96*N^2) := by
  have hN0 : 0 < N := by linarith
  have haN := (sargosQuartic_source_scale hN hα).2.1
  apply hγ.trans
  apply (div_le_div_iff₀ (by positivity : 0 < N^3) (by positivity : 0 < 96*N^2)).mpr
  nlinarith [mul_le_mul_of_nonneg_right haN (sq_nonneg N)]

theorem sargosQuarticLegendreRemainder_source_bound {N α γ y : ℝ}
    (hN : 9216 ≤ N) (hα : 1/Real.sqrt N ≤ α) (hγ : |γ| ≤ 1/N^3)
    (hy : y ∈ sargosQuarticSlopeRange N α γ) :
    |sargosQuarticLegendreRemainder N α γ y| ≤ 10240 := by
  have hN0 : 0 < N := by linarith
  have ha := sargosQuartic_source_scale hN hα
  have ha0 : 0 < α := ha.1
  calc
    _ ≤ 10240*|γ|^3*N^8/α^2 :=
      sargosQuarticLegendreRemainder_bound hN0 ha.1 (sargosQuartic_source_smallness hN hα hγ) hy
    _ ≤ 10240*(1/N^3)^3*N^8/α^2 := by gcongr
    _ = 10240/(N*α^2) := by field_simp
    _ ≤ 10240 := (div_le_iff₀ (by positivity)).mpr (by nlinarith [ha.2.2])

theorem sargosQuarticLegendreRemainderDerivative_source_bound {N α γ y : ℝ}
    (hN : 9216 ≤ N) (hα : 1/Real.sqrt N ≤ α) (hγ : |γ| ≤ 1/N^3)
    (hy : y ∈ sargosQuarticSlopeRange N α γ) :
    |sargosQuarticLegendreRemainderDerivative N α γ y| ≤ 16384/(α*N) := by
  have hN0 : 0 < N := by linarith
  have ha := sargosQuartic_source_scale hN hα
  have ha0 : 0 < α := ha.1
  calc
    _ ≤ 16384*|γ|^3*N^7/α^3 :=
      sargosQuarticLegendreRemainderDerivative_bound hN0 ha.1
        (sargosQuartic_source_smallness hN hα hγ) hy
    _ ≤ 16384*(1/N^3)^3*N^7/α^3 := by gcongr
    _ = (16384/(α*N))/(N*α^2) := by field_simp
    _ ≤ 16384/(α*N) :=
      (div_le_iff₀ (by positivity)).mpr
        (le_mul_of_one_le_right (by positivity) ha.2.2)

theorem sargosQuarticLegendreRemainder_source_hasDerivAt {N α γ y : ℝ}
    (hN : 9216 ≤ N) (hα : 1/Real.sqrt N ≤ α) (hγ : |γ| ≤ 1/N^3)
    (hy : y ∈ sargosQuarticSlopeRange N α γ) :
    HasDerivAt (sargosQuarticLegendreRemainder N α γ)
        (sargosQuarticLegendreRemainderDerivative N α γ y) y ∧
      |sargosQuarticLegendreRemainderDerivative N α γ y| ≤ 16384/(α*N) :=
  ⟨sargosQuarticLegendreRemainder_hasDerivAt (by linarith)
      (sargosQuartic_source_scale hN hα).1 (sargosQuartic_source_smallness hN hα hγ) hy,
    sargosQuarticLegendreRemainderDerivative_source_bound hN hα hγ hy⟩

end TaoTrudgianYang2025
