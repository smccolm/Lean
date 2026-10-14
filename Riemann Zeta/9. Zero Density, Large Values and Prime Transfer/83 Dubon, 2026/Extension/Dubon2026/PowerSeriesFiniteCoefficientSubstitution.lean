import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Order

/-! # The exact finite-degree dependence of one-variable substitution

The coefficient formula and the order of powers prove substitution stability
through a fixed degree. This is the univariate dependency required to pass
DUB-17's corrected semilinear Witt approximations to their actual limiting
series. No multivariate truncation infrastructure is needed.
-/
namespace Dubon2026
noncomputable section

/-- Agreement through degree m is preserved by actual power-series powers through that degree. -/
theorem powerSeries_coeff_pow_eq_of_coeff_eq_le
    {R : Type*} [CommRing R] {f g : PowerSeries R} (m : ℕ)
    (hfg : ∀ d ≤ m, PowerSeries.coeff d f = PowerSeries.coeff d g)
    (k d : ℕ) (hd : d ≤ m) : PowerSeries.coeff d (f ^ k) = PowerSeries.coeff d (g ^ k) := by
  induction k generalizing d with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro ij hij
    have hij' := Finset.mem_antidiagonal.mp hij
    rw [ih ij.1 (by omega), hfg ij.2 (by omega)]

/-- The degree-m coefficient of actual one-variable substitution depends only on coefficients through degree m when the inner series have zero constants. -/
theorem powerSeries_coeff_subst_eq_of_coeff_eq_le
    {R : Type*} [CommRing R] {f g b c : PowerSeries R}
    (hb : PowerSeries.constantCoeff b = 0) (hc : PowerSeries.constantCoeff c = 0)
    (m : ℕ) (hfg : ∀ d ≤ m, PowerSeries.coeff d f = PowerSeries.coeff d g)
    (hbc : ∀ d ≤ m, PowerSeries.coeff d b = PowerSeries.coeff d c) :
    PowerSeries.coeff m (PowerSeries.subst b f) =
      PowerSeries.coeff m (PowerSeries.subst c g) := by
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' hb),
    PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' hc)]
  apply finsum_congr
  intro k
  by_cases hk : k ≤ m
  · rw [hfg k hk, powerSeries_coeff_pow_eq_of_coeff_eq_le m hbc k m le_rfl]
  · have hmk : (m : ℕ∞) < (k : ℕ∞) := by exact_mod_cast Nat.lt_of_not_ge hk
    have hb0 := PowerSeries.coeff_of_lt_order m
      (hmk.trans_le (PowerSeries.le_order_pow_of_constantCoeff_eq_zero k hb))
    have hc0 := PowerSeries.coeff_of_lt_order m
      (hmk.trans_le (PowerSeries.le_order_pow_of_constantCoeff_eq_zero k hc))
    rw [hb0, hc0, smul_zero, smul_zero]

end
end Dubon2026
