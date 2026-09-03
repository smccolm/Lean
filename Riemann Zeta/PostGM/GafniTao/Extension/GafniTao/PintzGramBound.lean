import GafniTao.PintzPartialZeta

/-!
# The physical off-diagonal Gram bound in Pintz (4.12)

Pintz's selected ordinates are separated on the scale `lambda`, while the
finite Möbius cutoff is `exp (lambda + 3)`.  Consequently the shifted partial
zeta sum has two genuine regimes.  This module records both, rather than
pretending that the cutoff is always below the shifted height.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- Ford's arbitrary-cutoff bound when the cutoff is below the shifted
height. -/
noncomputable def pintzShortCutoffMajorant (sigma t : ℝ) : ℝ :=
  1 + fordQualitativeCoefficient *
    (|t| ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) *
      (1 + 1.569 * (3000000 : ℝ) ^ ((1 : ℝ) / 3) *
        Real.log |t| ^ ((2 : ℝ) / 3)))

/-- Euler--Maclaurin completion when the physical cutoff exceeds the shifted
height. -/
noncomputable def pintzLongCutoffMajorant
    (sigma : ℝ) (M : ℕ) (t : ℝ) : ℝ :=
  fordQualitativeGlobalCoefficient *
      |t| ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) *
      Real.log |t| ^ (2 / 3 : ℝ) +
    5 * (M : ℝ) ^ (1 - sigma)

noncomputable def pintzPartialZetaMajorant
    (sigma : ℝ) (M : ℕ) (t : ℝ) : ℝ :=
  max (pintzShortCutoffMajorant sigma t)
    (pintzLongCutoffMajorant sigma M t)

theorem norm_partialZeta_le_pintzMajorant
    {sigma t : ℝ} {M : ℕ}
    (hsigmaLower : 1 / 2 ≤ sigma) (hsigmaUpper : sigma ≤ 1)
    (ht : 3 ≤ |t|) (hMPos : 1 ≤ M) :
    ‖∑ n ∈ Finset.Icc 1 M,
        (n : ℂ) ^ (-fordComplexHeight sigma t)‖ ≤
      pintzPartialZetaMajorant sigma M t := by
  by_cases hcutoff : (M : ℝ) ≤ |t|
  · exact (norm_fordPartialSum_le_qualitative_general_abs
      (by linarith) hsigmaUpper (by linarith) hMPos hcutoff).trans
        (le_max_left _ _)
  · have hlong : |t| < (M : ℝ) := lt_of_not_ge hcutoff
    exact (norm_partialZeta_le_ford_add_endpoint
      hsigmaLower hsigmaUpper ht hMPos hlong).trans (le_max_right _ _)

/-- The exact shifted Gram entry from (4.12), bounded in both physical
cutoff regimes. -/
theorem norm_pintzGramCorrelation_le_majorant
    {xi t u : ℝ} {Y : ℕ}
    (hxi : 0 ≤ xi) (hxiUpper : xi ≤ 1 / 4)
    (hsep : 3 ≤ |u - t|) (hY : 1 ≤ Y) :
    ‖pintzGramCorrelation xi Y t u‖ ≤
      pintzPartialZetaMajorant (1 - 2 * xi) Y (u - t) := by
  rw [pintzGramCorrelation_eq_shifted_sum]
  have hsigmaLower : (1 / 2 : ℝ) ≤ 1 - 2 * xi := by linarith
  have hsigmaUpper : (1 - 2 * xi : ℝ) ≤ 1 := by linarith
  have hheight :
      fordComplexHeight (1 - 2 * xi) (u - t) =
        ((1 - 2 * xi : ℝ) : ℂ) + I * (u - t) := by
    simp [fordComplexHeight, mul_comm]
  rw [← hheight]
  exact norm_partialZeta_le_pintzMajorant
    hsigmaLower hsigmaUpper hsep hY

#print axioms norm_partialZeta_le_pintzMajorant
#print axioms norm_pintzGramCorrelation_le_majorant

end

end GafniTao
