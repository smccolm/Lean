import Dubon2026.IntegralInducedFundamentalVector
import Mathlib.Algebra.BigOperators.Intervals

/-! Exact dominant-weight decomposition into the original fundamental
weights and a determinant shift. Native finite telescoping is reused;
this supplies the exponents of an explicit nonzero regular-function
vector in the source integral induced module.
-/

namespace Dubon2026
noncomputable section

/-- Adjacent differences of the original weight telescope at every original finite index. -/
theorem integralWeight_adjacent_sum {n : ℕ} (mu : Fin (n + 1) → ℤ) (i : Fin (n + 1)) :
    (∑ j : Fin n, if j.succ ≤ i then mu j.succ - mu j.castSucc else 0) = mu i - mu 0 := by
  induction i using Fin.cases with
  | zero => simp
  | succ i =>
      calc
        (∑ j : Fin n, if j.succ ≤ i.succ then mu j.succ - mu j.castSucc else 0) =
            ∑ j ∈ Finset.Iic i, (mu j.succ - mu j.castSucc) := by
          rw [← Finset.sum_filter]
          congr 1
          ext j
          simp
        _ = mu i.succ - mu 0 := Fin.sum_Iic_sub i mu

/-- The nonnegative adjacent exponents for an original dominant integral weight. -/
def integralDominantWeightExponent {n : ℕ} (lam : Fin (n + 1) → ℤ) (j : Fin n) : ℕ :=
  (lam j.succ.rev - lam j.castSucc.rev).toNat

/-- Dominance makes each original adjacent exponent genuinely nonnegative, so passing to natural powers loses no information. -/
theorem integralDominantWeightExponent_coe {n : ℕ} (lam : Fin (n + 1) → ℤ)
    (hlam : Antitone lam) (j : Fin n) :
    (integralDominantWeightExponent lam j : ℤ) = lam j.succ.rev - lam j.castSucc.rev := by
  apply Int.toNat_of_nonneg
  apply sub_nonneg.mpr
  apply hlam
  exact Fin.rev_le_rev.mpr (Fin.castSucc_le_succ j)

/-- The original dominant tuple is exactly the sum of its fundamental weights with nonnegative exponents and its original last-weight determinant shift. -/
theorem integralDominantWeight_decomposition {n : ℕ} (lam : Fin (n + 1) → ℤ)
    (hlam : Antitone lam) (i : Fin (n + 1)) :
    lam i =
      (∑ j : Fin n, (integralDominantWeightExponent lam j : ℤ) *
        integralInducedFundamentalWeight (n + 1) j.succ i) + lam (0 : Fin (n + 1)).rev := by
  simp_rw [integralDominantWeightExponent_coe lam hlam, integralInducedFundamentalWeight,
    mul_ite, mul_one, mul_zero]
  rw [integralWeight_adjacent_sum (fun k => lam k.rev) i.rev, Fin.rev_rev]
  omega

end
end Dubon2026
