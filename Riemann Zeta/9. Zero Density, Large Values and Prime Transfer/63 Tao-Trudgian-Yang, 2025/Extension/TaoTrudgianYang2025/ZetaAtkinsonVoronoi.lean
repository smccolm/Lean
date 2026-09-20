import TaoTrudgianYang2025.ZetaDivisorLatticePhase

/-!
# Voronoi with the source's saddle-regulating lattice phase

The unchanged arithmetic source is now transformed using its actual
phase-adjusted continuous test. The previous unadjusted identities
remain valid, but their continuous saddle equations are different.
-/

noncomputable section

open Complex MeasureTheory Set
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

theorem ordinaryDivisorVoronoi_bessel {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    (∑' n : ℕ, divisorWeight n * g n) =
      (∫ x : ℝ in Ioi 0, ((Real.log x : ℂ) + 2 * Real.eulerMascheroniConstant) * g x) +
        (∑' n : ℕ, divisorWeight n * (-(2 * Real.pi) : ℂ) *
          ∫ x : ℝ in Ioi 0, g x * (dfiBesselY0 (4 * Real.pi * Real.sqrt (x * n)) : ℂ)) +
        ∑' n : ℕ, divisorWeight n * 4 *
          ∫ x : ℝ in Ioi 0, g x * (dfiBesselK0 (4 * Real.pi * Real.sqrt (x * n)) : ℂ) := by
  have hminus (n : ℕ) : divisorWeight n * dfiVoronoiMinusTransform 1 (mellin g) n =
      divisorWeight n * (-(2 * Real.pi) : ℂ) *
        ∫ x : ℝ in Ioi 0, g x * (dfiBesselY0 (4 * Real.pi * Real.sqrt (x * n)) : ℂ) := by
    by_cases hn : n = 0
    · simp [hn, divisorWeight]
    · have h := hg.dfiEquation29InitialMinusTransform_eq_bessel 1 (Nat.pos_of_ne_zero hn)
      change dfiVoronoiMinusTransform 1 (mellin g) n = _ at h
      rw [h]
      simp only [dfiVoronoiMinusBesselTransform, Nat.cast_one, div_one, mul_assoc]
  have hplus (n : ℕ) : divisorWeight n * dfiVoronoiPlusTransform 1 (mellin g) n =
      divisorWeight n * 4 *
        ∫ x : ℝ in Ioi 0, g x * (dfiBesselK0 (4 * Real.pi * Real.sqrt (x * n)) : ℂ) := by
    by_cases hn : n = 0
    · simp [hn, divisorWeight]
    · rw [dfiVoronoiPlusTransform_mellin_eq_bessel 1 n (Nat.pos_of_ne_zero hn) hg]
      simp only [dfiVoronoiPlusBesselTransform, Nat.cast_one, div_one, mul_assoc]
  rw [ordinaryDivisorVoronoi_native hg]
  simp_rw [hminus, hplus]

def zetaAtkinsonVoronoiMain (T G L : ℝ) : ℂ :=
  ∫ x : ℝ in Ioi 0, ((Real.log x : ℂ) + 2 * Real.eulerMascheroniConstant) *
    zetaAtkinsonDivisorTest T G L x

def zetaAtkinsonBesselMinus (T G L : ℝ) : ℂ :=
  ∑' n : ℕ, divisorWeight n * (-(2 * Real.pi) : ℂ) *
    ∫ x : ℝ in Ioi 0, zetaAtkinsonDivisorTest T G L x *
      (dfiBesselY0 (4 * Real.pi * Real.sqrt (x * n)) : ℂ)

def zetaAtkinsonBesselPlusTerm (T G L : ℝ) (n : ℕ) : ℂ :=
  divisorWeight n * 4 * ∫ x : ℝ in Ioi 0, zetaAtkinsonDivisorTest T G L x *
    (dfiBesselK0 (4 * Real.pi * Real.sqrt (x * n)) : ℂ)

def zetaAtkinsonBesselPlus (T G L : ℝ) : ℂ := ∑' n : ℕ, zetaAtkinsonBesselPlusTerm T G L n

theorem zetaSmoothDivisorSum_eq_atkinson_bessel {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) :
    zetaSmoothDivisorSum T G L = zetaAtkinsonVoronoiMain T G L +
      zetaAtkinsonBesselMinus T G L + zetaAtkinsonBesselPlus T G L := by
  rw [zetaSmoothDivisorSum_eq_atkinson_test]
  exact ordinaryDivisorVoronoi_bessel (zetaAtkinsonDivisorVoronoiTest hT hG hL)

theorem exists_zetaSquarePhysicalGaussian_atkinson_approximation {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → 0 < G → G ≤ T ^ (1 / 2 - δ) →
      |(∫ t : ℝ, zetaGaussianWeight T G t * zetaMomentCriticalNorm t ^ 2) -
        2 * (zetaAtkinsonVoronoiMain T G (Real.log T) +
          zetaAtkinsonBesselMinus T G (Real.log T) +
          zetaAtkinsonBesselPlus T G (Real.log T)).re| ≤ C * G * Real.log T := by
  obtain ⟨C, hC, T₀, hT₀, hbound⟩ := exists_zetaSquareGaussianMean_smooth_approximation hδ
  refine ⟨C, hC, T₀, hT₀, ?_⟩
  intro T G hT hG hupper
  have hT8 := hT₀.trans hT
  rw [← zetaSquareGaussianMean_eq_physical T hG,
    ← zetaSmoothDivisorSum_eq_atkinson_bessel (by linarith : 0 < T) hG (Real.log_pos (by linarith))]
  exact hbound T G hT hG hupper

theorem exists_zetaSquareLocalMean_le_atkinson_bessel {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → 0 < G → G ≤ T ^ (1 / 2 - δ) →
      (∫ t in T - G..T + G, zetaMomentCriticalNorm t ^ 2) ≤
        2 * Real.exp 1 * (zetaAtkinsonVoronoiMain T G (Real.log T) +
          zetaAtkinsonBesselMinus T G (Real.log T) + zetaAtkinsonBesselPlus T G (Real.log T)).re +
            C * G * Real.log T := by
  obtain ⟨C, hC, T₀, hT₀, hbound⟩ := exists_zetaSquareLocalMean_le_smooth_divisor hδ
  refine ⟨C, hC, T₀, hT₀, ?_⟩
  intro T G hT hG hupper
  have hT8 := hT₀.trans hT
  rw [← zetaSmoothDivisorSum_eq_atkinson_bessel (by linarith : 0 < T) hG (Real.log_pos (by linarith))]
  exact hbound T G hT hG hupper

end TaoTrudgianYang2025
