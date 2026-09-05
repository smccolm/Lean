import GafniTao.Pintz2023WeightedBlockSign
import GafniTao.Pintz2023Localization

/-!
# Complex-power interface to Pintz's weighted block

This is the exact bridge between the complex-power notation used after the
Möbius factorization in (4.14) and the real-weighted block in Corollary 3.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

noncomputable def pintz2023ComplexWeightedBlock
    (xi : ℝ) (N R : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc N R,
    (n : ℂ) ^ (-(((1 - xi : ℝ) : ℂ) + I * (t : ℂ)))

theorem pintz2023ComplexWeightedBlock_eq
    (xi : ℝ) (N R : ℕ) (t : ℝ) :
    pintz2023ComplexWeightedBlock xi N R t =
      pintz2023WeightedBlock xi N R t := by
  classical
  unfold pintz2023ComplexWeightedBlock pintz2023WeightedBlock
  apply Finset.sum_congr rfl
  intro n hn
  have hnPos : 0 < n := by
    have := (Finset.mem_Ioc.mp hn).1
    omega
  calc
    (n : ℂ) ^ (-(((1 - xi : ℝ) : ℂ) + I * (t : ℂ))) =
        (n : ℂ) ^ (-((1 - xi : ℝ) : ℂ)) *
          (n : ℂ) ^ (-(t : ℂ) * I) := by
            symm
            simpa only [mul_comm I (t : ℂ)] using
              pintz2023_factorized_term hnPos (1 - xi) t
    _ = (((n : ℝ) ^ (-(1 - xi)) : ℝ) : ℂ) *
          (n : ℂ) ^ (-(t : ℂ) * I) := by
            rw [Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ n)]
    _ = (n : ℝ) ^ (-(1 - xi)) •
          (n : ℂ) ^ (-(t : ℂ) * I) := by
            rw [Complex.real_smul]

/-- Corollary 3 at either sign of the ordinate. -/
theorem pintz2023_corollary_three_abs
    (r : ℕ) (epsilon B : ℝ) (hr : 3 ≤ r)
    (hepsilon : 0 < epsilon) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (xi : ℝ) (N R : ℕ) (t T : ℝ),
      xi ≤ pintz2023HBAlpha r - 6 * epsilon →
      0 < 1 - ((r : ℝ) - 1) * xi - 6 * (r : ℝ) * epsilon →
      0 < N → N < R → R ≤ 2 * N →
      0 < |t| → |t| ≤ T → 1 ≤ T →
      pintz2023CriticalScale r xi epsilon T ≤ (N : ℝ) →
      (N : ℝ) ≤ B * |t| ^ (2 / (r : ℝ)) →
      ‖pintz2023ComplexWeightedBlock xi N R t‖ ≤
        C * (N : ℝ) ^ (-3 * epsilon) := by
  obtain ⟨C, hC, hbound⟩ :=
    pintz2023_corollary_three_native r epsilon B hr hepsilon hB
  refine ⟨C, hC, ?_⟩
  intro xi N R t T hxi hden hN hNR hR ht htT hT hcritical hscale
  rw [pintz2023ComplexWeightedBlock_eq, ← norm_pintz2023WeightedBlock_abs]
  exact hbound xi N R |t| T hxi hden hN hNR hR ht htT hT
    hcritical hscale

#print axioms pintz2023ComplexWeightedBlock_eq
#print axioms pintz2023_corollary_three_abs

end

end GafniTao
