import Dubon2026.DirichletZeros
import Dubon2026.JessenMean

/-! # Real coefficient weights translate the actual Dirichlet truncation and its zeros -/

namespace Dubon2026

open Complex

noncomputable section

/-- Multiply the actual coefficients by the positive-index complex power n^c. -/
def shiftedCoefficients (a : ℕ → ℂ) (c : ℝ) (n : ℕ) : ℂ := a n * (n : ℂ) ^ (c : ℂ)

theorem shiftedCoefficients_one (a : ℕ → ℂ) (c : ℝ) :
    shiftedCoefficients a c 1 = a 1 := by simp [shiftedCoefficients]

theorem dirichletSum_shiftedCoefficients (a : ℕ → ℂ) (N : ℕ) (c : ℝ) (s : ℂ) :
    dirichletSum (shiftedCoefficients a c) N s = dirichletSum a N (s - c) := by
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : (n : ℂ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 from Nat.ne_zero_of_lt (lt_of_lt_of_le Nat.zero_lt_one
      (Finset.mem_Icc.mp hn).1))
  rw [shiftedCoefficients, mul_assoc, ← Complex.cpow_add _ _ hn0]
  congr 2
  ring

theorem coefficientSupport_shiftedCoefficients (a : ℕ → ℂ) (N : ℕ) (c : ℝ) :
    coefficientSupport (shiftedCoefficients a c) N = coefficientSupport a N := by
  ext n
  rw [mem_coefficientSupport, mem_coefficientSupport]
  by_cases hn : 1 ≤ n
  · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hp : (n : ℂ) ^ (c : ℂ) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hn0)
    simp only [shiftedCoefficients, mul_ne_zero_iff]
    exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.1⟩, fun h => ⟨h.1, h.2.1, h.2.2, hp⟩⟩
  · simp only [hn, false_and]

theorem lastIndex_shiftedCoefficients (a : ℕ → ℂ) (N : ℕ) (c : ℝ) :
    lastIndex (shiftedCoefficients a c) N = lastIndex a N := by
  simp only [lastIndex, coefficientSupport_shiftedCoefficients]

theorem zeroMultiplicity_shiftedCoefficients (a : ℕ → ℂ) (N : ℕ) (c : ℝ) (s : ℂ) :
    zeroMultiplicity (shiftedCoefficients a c) N s = zeroMultiplicity a N (s - c) := by
  have he : dirichletSum (shiftedCoefficients a c) N =
      dirichletSum a N ∘ (fun w : ℂ => w - c) :=
    funext (dirichletSum_shiftedCoefficients a N c)
  have hg : AnalyticAt ℂ (fun w : ℂ => w - c) s := analyticAt_id.sub analyticAt_const
  have hd : deriv (fun w : ℂ => w - c) s ≠ 0 := by
    have hd₀ : HasDerivAt (fun w : ℂ => w - c) 1 s := (hasDerivAt_id s).sub_const _
    rw [hd₀.deriv]
    exact one_ne_zero
  simp only [zeroMultiplicity, analyticOrderNatAt, he,
    analyticOrderAt_comp_of_deriv_ne_zero hg hd]

theorem verticalLogMean_shiftedCoefficients (a : ℕ → ℂ) (N : ℕ) (c σ T : ℝ) :
    verticalLogMean (shiftedCoefficients a c) N σ T = verticalLogMean a N (σ - c) T := by
  unfold verticalLogMean
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [dirichletSum_shiftedCoefficients]
  have he : (σ : ℂ) + I * t - c = ((σ - c : ℝ) : ℂ) + I * t := by
    push_cast
    ring
  rw [he]

theorem jessenFunction_shiftedCoefficients (a : ℕ → ℂ) (N : ℕ) (c σ : ℝ) :
    jessenFunction (shiftedCoefficients a c) N σ = jessenFunction a N (σ - c) := by
  unfold jessenFunction
  congr 1
  funext T
  exact verticalLogMean_shiftedCoefficients a N c σ T

end

end Dubon2026
