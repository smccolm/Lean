import TaoTrudgianYang2025.SargosIntegerDyadicTrim

/-! The rounded dyadic scale linked to the actual quartic source frequencies. -/

noncomputable section

open Set

namespace TaoTrudgianYang2025

def sargosQuarticRoundedDualScale (N Δ : ℝ) : ℕ := ⌊2*Δ*N⌋₊

theorem sargosQuarticRoundedDualScale_bounds {N Δ : ℝ}
    (hN : 9216 ≤ N) (hΔ : 1/Real.sqrt N ≤ Δ) :
    192 ≤ sargosQuarticRoundedDualScale N Δ ∧
      (sargosQuarticRoundedDualScale N Δ : ℝ) ≤ 2*Δ*N ∧
      2*Δ*N < (sargosQuarticRoundedDualScale N Δ : ℝ)+1 ∧
      Δ*N ≤ (sargosQuarticRoundedDualScale N Δ : ℝ) := by
  have hs := sargosQuartic_source_scale hN hΔ
  have hM : 192 ≤ 2*Δ*N := by nlinarith only [hs.2.1]
  have hfloor := Nat.floor_le (show 0 ≤ 2*Δ*N by linarith)
  have hnext := Nat.lt_floor_add_one (2*Δ*N)
  refine ⟨Nat.le_floor hM,hfloor,hnext,?_⟩
  change Δ*N ≤ (⌊2*Δ*N⌋₊ : ℝ)
  nlinarith only [hs.2.1,hnext]

theorem sargosQuartic_closed_slopes_dyadic_bounds {N Δ α γ : ℝ}
    (hN : 0 < N) (hΔα : Δ ≤ α) (hαΔ : α ≤ 2*Δ) (hγ : |γ| ≤ 1/N^3) :
    2*Δ*N-4 ≤ sargosQuarticSlope α γ N ∧
      sargosQuarticSlope α γ (2*N) ≤ 8*Δ*N+32 := by
  have hc := abs_le.mp (sargosQuartic_source_cubic_bound hN hγ)
  have hl := mul_le_mul_of_nonneg_right hΔα hN.le
  have hu := mul_le_mul_of_nonneg_right hαΔ hN.le
  unfold sargosQuarticSlope
  constructor <;> nlinarith only [hc.1,hc.2,hl,hu]

theorem sargosQuarticRoundedFrequency_bounds {N Δ α γ : ℝ}
    (hN : 9216 ≤ N) (hΔ : 1/Real.sqrt N ≤ Δ) (hα : α ∈ Icc Δ (2*Δ))
    (hγ : |γ| ≤ 1/N^3) :
    (sargosQuarticRoundedDualScale N Δ : ℤ)-4 ≤ ⌈sargosQuarticSlope α γ N⌉ ∧
      ⌊sargosQuarticSlope α γ (2*N)⌋ ≤ 4*(sargosQuarticRoundedDualScale N Δ : ℤ)+35 := by
  let m := sargosQuarticRoundedDualScale N Δ
  have hs := sargosQuarticRoundedDualScale_bounds hN hΔ
  have hq := sargosQuartic_closed_slopes_dyadic_bounds (by linarith : 0 < N) hα.1 hα.2 hγ
  have hl := Int.le_ceil (sargosQuarticSlope α γ N)
  have hu := Int.floor_le (sargosQuarticSlope α γ (2*N))
  constructor
  · have hh : (m : ℝ)-4 ≤ (⌈sargosQuarticSlope α γ N⌉ : ℝ) := by
      have hm : (m : ℝ) ≤ 2*Δ*N := hs.2.1
      linarith only [hm,hq.1,hl]
    exact_mod_cast hh
  · have hh : (⌊sargosQuarticSlope α γ (2*N)⌋ : ℝ) < 4*(m : ℝ)+36 := by
      have hm : 2*Δ*N < (m : ℝ)+1 := hs.2.2.1
      linarith only [hm,hq.2,hu]
    have hi : ⌊sargosQuarticSlope α γ (2*N)⌋ < 4*(m : ℤ)+36 := by exact_mod_cast hh
    change _ ≤ 4*(m : ℤ)+35
    omega

theorem sargosQuarticStationaryFrequencies_subset_rounded {N Δ α γ : ℝ}
    (hN : 9216 ≤ N) (hΔ : 1/Real.sqrt N ≤ Δ) (hα : α ∈ Icc Δ (2*Δ))
    (hγ : |γ| ≤ 1/N^3) :
    sargosQuarticStationaryFrequencies N α γ ⊆
      Finset.Icc ((sargosQuarticRoundedDualScale N Δ : ℤ)-4)
        (4*(sargosQuarticRoundedDualScale N Δ : ℤ)+35) := by
  have hb := sargosQuarticRoundedFrequency_bounds hN hΔ hα hγ
  intro y hy
  simp only [sargosQuarticStationaryFrequencies,Finset.mem_Icc] at hy ⊢
  exact ⟨hb.1.trans hy.1,hy.2.trans hb.2⟩

end TaoTrudgianYang2025

