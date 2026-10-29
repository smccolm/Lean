import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! DUB-17/18 -> original Gamma1 degree preservation -> even-weight
slash integrality -> peaked auxiliary trace. These are the exact numerical
and coefficient prerequisites used to isolate one slash coefficient from
the trace. Adapted from anthropics/fermats-last-theorem, Apache-2.0,
revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularForm_qExpansion_slash_coeff_mem_of_peaked_auxiliary. -/
namespace Dubon2026.SourceFunctionField.IntegralTrace
theorem coeff_pow_eq_zero_of_lt {K : Type*} [CommRing K] (U : PowerSeries K) (m₀ r : ℕ)
    (hU : ∀ i : ℕ, i < m₀ → PowerSeries.coeff i U = 0) (i : ℕ) (hi : i < r * m₀) :
    PowerSeries.coeff i (U ^ r) = 0 := by
  have hdvd : PowerSeries.X ^ m₀ ∣ U := by
    rw [PowerSeries.X_pow_dvd_iff]
    exact hU
  obtain ⟨V, hV⟩ := hdvd
  rw [hV, mul_pow, ← pow_mul, mul_comm m₀ r, PowerSeries.coeff_X_pow_mul']
  rw [if_neg (not_le.mpr hi)]

theorem coeff_pow_mul {K : Type*} [CommRing K] (U : PowerSeries K) (m₀ r : ℕ)
    (hU : ∀ i : ℕ, i < m₀ → PowerSeries.coeff i U = 0) :
    PowerSeries.coeff (r * m₀) (U ^ r) = (PowerSeries.coeff m₀ U) ^ r := by
  have hdvd : PowerSeries.X ^ m₀ ∣ U := by
    rw [PowerSeries.X_pow_dvd_iff]
    exact hU
  obtain ⟨V, hV⟩ := hdvd
  subst hV
  rw [mul_pow, ← pow_mul, mul_comm m₀ r, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    PowerSeries.coeff_zero_eq_constantCoeff, map_pow, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    PowerSeries.coeff_zero_eq_constantCoeff]

theorem coeff_mul_mem {R : Subring ℂ} {P Q : PowerSeries ℂ} (hP : ∀ i, PowerSeries.coeff i P ∈ R)
    (hQ : ∀ i, PowerSeries.coeff i Q ∈ R) (i : ℕ) : PowerSeries.coeff i (P * Q) ∈ R := by
  rw [PowerSeries.coeff_mul]
  exact R.sum_mem fun p _ => R.mul_mem (hP _) (hQ _)

theorem coeff_pow_mem {R : Subring ℂ} {P : PowerSeries ℂ} (hP : ∀ i, PowerSeries.coeff i P ∈ R) (r : ℕ) (i : ℕ) :
    PowerSeries.coeff i (P ^ r) ∈ R := by
  induction r generalizing i with
  | zero => simp only [pow_zero, PowerSeries.coeff_one]; split_ifs <;> simp [R.one_mem, R.zero_mem]
  | succ r ih => rw [pow_succ]; exact coeff_mul_mem ih hP i

end Dubon2026.SourceFunctionField.IntegralTrace
