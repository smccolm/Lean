import Dubon2026.SourceJModularQuotient
import Dubon2026.ModularDegeneracyCoefficients

/-! DUB-17/18 -> analytic realization of the original modular field ->
actual generator ratios. Existing cusp degeneracy maps already implement
f(dz) and prove its sparse Fourier coefficients. This bridge identifies
their full Laurent expansions with the original qExpand homomorphism,
including all negative coefficients. No new degeneracy construction is
needed; multiplying both sides of the j ratio by the discriminant makes
these existing cusp-form maps sufficient.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

theorem cuspDegeneracyMap_laurent {M N : ℕ} (d : ℕ) [NeZero d]
    (h : d * M ∣ N) {k : ℤ} (f : CuspForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) k) :
    (qExpansion 1 (cuspDegeneracyMap d h k f : UpperHalfPlane → ℂ) : LaurentSeries ℂ) =
      qExpand ℂ d (qExpansion 1 (f : UpperHalfPlane → ℂ) : LaurentSeries ℂ) := by
  ext n
  by_cases hd : (d : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := hd
    rw [qExpand_coeff_mul]
    by_cases hm : 0 ≤ m
    · lift m to ℕ using hm
      rw [← Nat.cast_mul, HahnSeries.ofPowerSeries_apply_coeff,
        HahnSeries.ofPowerSeries_apply_coeff]
      change cuspCoefficients (cuspDegeneracyMap d h k f) (d * m) = cuspCoefficients f m
      rw [cuspDegeneracyMap_coeff, if_pos (dvd_mul_right d m),
        Nat.mul_div_cancel_left m (Nat.pos_of_neZero d)]
    · rw [ofPowerSeries_coeff_of_neg _ (mul_neg_of_pos_of_neg
        (by exact_mod_cast Nat.pos_of_neZero d) (lt_of_not_ge hm)),
        ofPowerSeries_coeff_of_neg _ (lt_of_not_ge hm)]
  · rw [qExpand_coeff_of_not_dvd d _ hd]
    rcases le_or_gt 0 n with hn | hn
    · lift n to ℕ using hn
      rw [HahnSeries.ofPowerSeries_apply_coeff]
      change cuspCoefficients (cuspDegeneracyMap d h k f) n = 0
      rw [cuspDegeneracyMap_coeff, if_neg (fun hdn => hd (Int.natCast_dvd_natCast.mpr hdn))]
    · exact ofPowerSeries_coeff_of_neg _ hn

end
end Dubon2026.SourceFunctionField
