import Dubon2026.SourceModularCoefficientHurwitzCuspBound

/-! DUB-17/18 -> good reduction -> reverse genus in characteristics two
and three. The only remaining mathematical input is the displayed finite
differential contribution; canonical degree, coordinate degree, cusp count
and Hurwitz are derived. The wild contribution is still an open obligation. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve SourceLevelProjective KaehlerDifferential
variable (N : ℕ) [NeZero N] (K : Type*) [Field K] [IsAlgClosed K]

theorem coeff_genus_lower_of_wild_differential_contribution (hNK : (N : K) ≠ 0)
    (S : Finset (Place K (modularFunctionFieldCoeff N K)))
    (hS : ∀ v ∈ S, 0 ≤ v.ord (jCoeff N K))
    (hC : 7 * (dedekindPsi N : ℤ) - 3 * (nuTwo N : ℤ) - 4 * (nuThree N : ℤ) ≤
      6 * (∑ v ∈ S, v.ordDifferential (D K (modularFunctionFieldCoeff N K) (jCoeff N K)))) :
    genusFormula N ≤ (genusFF K (modularFunctionFieldCoeff N K) : ℚ) := by
  have h := coeff_hurwitz_differential_cusp_bound N K hNK S hS
  have hc : 7 * (dedekindPsi N : ℤ) - 3 * (nuTwo N : ℤ) - 4 * (nuThree N : ℤ) ≤
      6 * (2 * (genusFF K (modularFunctionFieldCoeff N K) : ℤ) - 2 +
        (dedekindPsi N : ℤ) + (cuspCount N : ℤ)) :=
    hC.trans (mul_le_mul_of_nonneg_left h (by norm_num))
  have hq : 7 * (dedekindPsi N : ℚ) - 3 * (nuTwo N : ℚ) - 4 * (nuThree N : ℚ) ≤
      6 * (2 * (genusFF K (modularFunctionFieldCoeff N K) : ℚ) - 2 +
        (dedekindPsi N : ℚ) + (cuspCount N : ℚ)) := by exact_mod_cast hc
  unfold genusFormula
  linarith

end
end Dubon2026.SourceFunctionField
