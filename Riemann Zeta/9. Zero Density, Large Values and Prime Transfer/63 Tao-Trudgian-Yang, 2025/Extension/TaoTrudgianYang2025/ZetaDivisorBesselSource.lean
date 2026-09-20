import TaoTrudgianYang2025.ZetaSquareVoronoiSource
import GuthMaynard.DFIEquation29

/-!
# Literal Bessel realization of the actual zeta source

Both identifications consume the constructed compact smooth test and
the native Mellin/Bessel bridges. The positive integer restriction is
handled explicitly: the ordinary divisor weight at zero vanishes.
This is source entry, not the still-needed uniform oscillatory estimate.
-/

noncomputable section

open Complex MeasureTheory Set
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

def zetaDivisorBesselMinus (T G L : ℝ) : ℂ :=
  ∑' n : ℕ, divisorWeight n * (-(2 * Real.pi) : ℂ) *
    ∫ x : ℝ in Ioi 0, zetaSmoothDivisorTest T G L x *
      (dfiBesselY0 (4 * Real.pi * Real.sqrt (x * n)) : ℂ)

def zetaDivisorBesselPlus (T G L : ℝ) : ℂ :=
  ∑' n : ℕ, divisorWeight n * 4 *
    ∫ x : ℝ in Ioi 0, zetaSmoothDivisorTest T G L x *
      (dfiBesselK0 (4 * Real.pi * Real.sqrt (x * n)) : ℂ)

theorem zetaDivisorVoronoiMinus_eq_bessel {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) :
    zetaDivisorVoronoiMinus T G L = zetaDivisorBesselMinus T G L := by
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · simp [hn, divisorWeight]
  · have h := (zetaSmoothDivisorVoronoiTest hT hG hL).dfiEquation29InitialMinusTransform_eq_bessel
      1 (Nat.pos_of_ne_zero hn)
    change dfiVoronoiMinusTransform 1 (mellin (zetaSmoothDivisorTest T G L)) n = _ at h
    rw [h]
    simp only [dfiVoronoiMinusBesselTransform, Nat.cast_one, div_one, mul_assoc]

theorem zetaDivisorVoronoiPlus_eq_bessel {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) :
    zetaDivisorVoronoiPlus T G L = zetaDivisorBesselPlus T G L := by
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · simp [hn, divisorWeight]
  · rw [dfiVoronoiPlusTransform_mellin_eq_bessel 1 n (Nat.pos_of_ne_zero hn)
      (zetaSmoothDivisorVoronoiTest hT hG hL)]
    simp only [dfiVoronoiPlusBesselTransform, Nat.cast_one, div_one, mul_assoc]

theorem zetaSmoothDivisorSum_eq_bessel {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) :
    zetaSmoothDivisorSum T G L = zetaDivisorVoronoiMain T G L +
      zetaDivisorBesselMinus T G L + zetaDivisorBesselPlus T G L := by
  rw [zetaSmoothDivisorSum_eq_voronoi hT hG hL, zetaDivisorVoronoiMinus_eq_bessel hT hG hL,
    zetaDivisorVoronoiPlus_eq_bessel hT hG hL]

theorem exists_zetaSquarePhysicalGaussian_bessel_approximation {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → 0 < G → G ≤ T ^ (1 / 2 - δ) →
      |(∫ t : ℝ, zetaGaussianWeight T G t * zetaMomentCriticalNorm t ^ 2) -
        2 * (zetaDivisorVoronoiMain T G (Real.log T) +
          zetaDivisorBesselMinus T G (Real.log T) +
          zetaDivisorBesselPlus T G (Real.log T)).re| ≤ C * G * Real.log T := by
  obtain ⟨C, hC, T₀, hT₀, hbound⟩ := exists_zetaSquarePhysicalGaussian_voronoi_approximation hδ
  refine ⟨C, hC, T₀, hT₀, ?_⟩
  intro T G hT hG hwidth
  have hT8 := hT₀.trans hT
  rw [← zetaDivisorVoronoiMinus_eq_bessel (by linarith : 0 < T) hG (Real.log_pos (by linarith)),
    ← zetaDivisorVoronoiPlus_eq_bessel (by linarith : 0 < T) hG (Real.log_pos (by linarith))]
  exact hbound T G hT hG hwidth

theorem exists_zetaSquareLocalMean_le_bessel {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → 0 < G → G ≤ T ^ (1 / 2 - δ) →
      (∫ t in T - G..T + G, zetaMomentCriticalNorm t ^ 2) ≤
        2 * Real.exp 1 * (zetaDivisorVoronoiMain T G (Real.log T) +
          zetaDivisorBesselMinus T G (Real.log T) + zetaDivisorBesselPlus T G (Real.log T)).re +
            C * G * Real.log T := by
  obtain ⟨C, hC, T₀, hT₀, hbound⟩ := exists_zetaSquareLocalMean_le_voronoi hδ
  refine ⟨C, hC, T₀, hT₀, ?_⟩
  intro T G hT hG hwidth
  have hT8 := hT₀.trans hT
  rw [← zetaDivisorVoronoiMinus_eq_bessel (by linarith : 0 < T) hG (Real.log_pos (by linarith)),
    ← zetaDivisorVoronoiPlus_eq_bessel (by linarith : 0 < T) hG (Real.log_pos (by linarith))]
  exact hbound T G hT hG hwidth

end TaoTrudgianYang2025
