import Dubon2026.SourceOriginalCanonicalFiberDegree
import Dubon2026.SourceOriginalRiemannRoch

/-! DUB-17/18 -> original parabolic Hecke realization -> period surjectivity
-> matching cusp-form lower dimension. The actual original complex function
field has the classical numerical genus, and its regular differentials have
that dimension. This assembles proved Riemann--Roch, exact local j-orders,
actual exceptional fiber counts and cusps; no genus or dimension premise is
supplied. The analytic map from these differentials to cusp forms remains
the next required comparison.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve

theorem six_mul_original_jCanonical_degree (N : ℕ) [NeZero N] :
    6 * Divisor.degree (originalCanonicalDivisor N ℂ (D_jOver_ne_zero N ℂ)) =
      (SourceLevelProjective.dedekindPsi N : ℤ) - 3 * SourceLevelProjective.nuTwo N -
        4 * SourceLevelProjective.nuThree N - 6 * SourceLevelProjective.cuspCount N := by
  have h2 : (2 : ℤ) * Nat.card {v : Place ℂ (modularFunctionFieldOver N ℂ) //
      0 < v.ord (jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) 1728)} =
        SourceLevelProjective.dedekindPsi N + SourceLevelProjective.nuTwo N := by
    exact_mod_cast two_mul_card_original_j_1728_fiber N
  have h3 : (3 : ℤ) * Nat.card {v : Place ℂ (modularFunctionFieldOver N ℂ) //
      0 < v.ord (jOver N ℂ)} =
        SourceLevelProjective.dedekindPsi N + 2 * SourceLevelProjective.nuThree N := by
    exact_mod_cast three_mul_card_original_j_zero_fiber N
  rw [original_jCanonical_degree_eq_fiber_cards]
  omega

theorem originalGenus_eq_genusFormula (N : ℕ) [NeZero N] :
    (originalGenus N ℂ : ℚ) = SourceLevelProjective.genusFormula N := by
  have hd := original_canonical_degree_eq_zero_index N ℂ (D_jOver_ne_zero N ℂ)
  rw [← originalGenus_eq_zero_index] at hd
  have hn := six_mul_original_jCanonical_degree N
  rw [hd] at hn
  have hq : (6 : ℚ) * (2 * (originalGenus N ℂ : ℚ) - 2) =
      SourceLevelProjective.dedekindPsi N - 3 * SourceLevelProjective.nuTwo N -
        4 * SourceLevelProjective.nuThree N - 6 * SourceLevelProjective.cuspCount N := by
    exact_mod_cast hn
  unfold SourceLevelProjective.genusFormula
  linarith

theorem finrank_original_regularDifferentials_eq_genusFormula (N : ℕ) [NeZero N] :
    (Module.finrank ℂ (regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) : ℚ) =
      SourceLevelProjective.genusFormula N := by
  rw [finrank_original_regularDifferentials_eq_genus, originalGenus_eq_genusFormula]

end
end Dubon2026.SourceFunctionField
